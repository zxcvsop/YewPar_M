#ifndef SEARCHMANAGER_COMPONENT_HPP
#define SEARCHMANAGER_COMPONENT_HPP

#include <iterator>                                              // for advance
#include <memory>                                                // for allo...
#include <random>                                                // for defa...
#include <vector>                                                // for vector
#include <utility>                                               // for vector
#include <queue>
#include <unordered_map>
#include "hpx/lcos/async.hpp"                                    // for async
#include "hpx/lcos/detail/future_data.hpp"                       // for task...
#include "hpx/lcos/detail/promise_lco.hpp"                       // for prom...
#include "hpx/lcos/future.hpp"                                   // for future
#include "hpx/lcos/local/channel.hpp"                            // for future
#include "hpx/runtime/actions/basic_action.hpp"                  // for make...
#include "hpx/runtime/actions/component_action.hpp"              // for HPX_...
#include "hpx/runtime/actions/transfer_action.hpp"               // for tran...
#include "hpx/runtime/actions/transfer_continuation_action.hpp"  // for tran...
#include "hpx/runtime/components/new.hpp"                        // for loca...
#include "hpx/runtime/components/server/component_base.hpp"      // for comp...
#include "hpx/runtime/components/server/locking_hook.hpp"        // for lock...
#include "hpx/runtime/find_here.hpp"                             // for find...
#include "hpx/runtime/naming/id_type.hpp"                        // for id_type
#include "hpx/runtime/naming/name.hpp"                           // for intr...
#include "hpx/runtime/serialization/binary_filter.hpp"           // for bina...
#include "hpx/runtime/serialization/serialize.hpp"               // for oper...
#include "hpx/runtime/serialization/shared_ptr.hpp"
#include "hpx/runtime/threads/executors/current_executor.hpp"    // for curr...
#include "hpx/runtime/threads/thread_data_fwd.hpp"               // for get_...
#include "hpx/traits/is_action.hpp"                              // for is_a...
#include "hpx/traits/needs_automatic_registration.hpp"           // for need...
#include "hpx/util/bind.hpp"                                     // for bound
#include "hpx/util/function.hpp"                                 // for func...
#include "hpx/util/unused.hpp"                                   // for unus...
#include "hpx/util/tuple.hpp"
#include <boost/optional.hpp>
#include <boost/serialization/optional.hpp>

namespace hpx { namespace serialization {
    template <typename Archive, typename SearchInfo>
    void serialize(Archive & ar, boost::optional<hpx::util::tuple<SearchInfo, int, hpx::naming::id_type> > & x, const unsigned int version) {
  ar & x;
}}}

namespace workstealing {

// The SearchManager component allows steals to happen directly within a
// searching thread. The SearchManager maintains a list of active threads and
// uses this to perform steals when work is requested from the scheduler. Thread
// response is generic allowing responses to be enumeration Nodes, B&B Nodes or
// even paths for recompute based skeletons
template <typename SearchInfo, typename FuncToCall>
class SearchManager: public hpx::components::locking_hook<
  hpx::components::component_base<SearchManager<SearchInfo, FuncToCall> > > {

 private:

  // Information returned on a steal from a thread
  using Response_t    = boost::optional<hpx::util::tuple<SearchInfo, int, hpx::naming::id_type> >;

  // Information shared between a thread and the manager. We set the atomic on a steal and then use the channel to await a response
  using SharedState_t = std::pair<std::atomic<bool>, hpx::lcos::local::one_element_channel<Response_t> >;

  // (internal) Id's of currently running threads, for managing the active map
  std::queue<unsigned> activeIds;

  // Active thread shared states
  std::unordered_map<unsigned, std::shared_ptr<SharedState_t> > active;

  // Shared states of threads currently being stolen from
  std::unordered_map<unsigned, std::shared_ptr<SharedState_t> > inactive;

  // Pointers to SearchManagers on other localities
  std::vector<hpx::naming::id_type> distributedSearchManagers;

  // Try to steal from a thread on another (random) locality
  Response_t tryDistributedSteal() {
    auto victim = distributedSearchManagers.begin();

    std::uniform_int_distribution<int> rand(0, distributedSearchManagers.size() - 1);
    std::default_random_engine randGenerator;
    std::advance(victim, rand(randGenerator));

    return hpx::async<getLocalWork_action>(*victim).get();
  }

 public:

  SearchManager() {
    for (auto i = 0; i < hpx::get_os_thread_count(); ++i) {
      activeIds.push(i);
    }
  }

  // Notify this search manager of the globalId's of potential steal victims
  void registerDistributedManagers(std::vector<hpx::naming::id_type> distributedSearchMgrs) {
    distributedSearchManagers = distributedSearchMgrs;
  }
  HPX_DEFINE_COMPONENT_ACTION(SearchManager, registerDistributedManagers);

  // Try to get work from a (random) thread running on this locality
  Response_t getLocalWork() {
    if (active.empty()) {
      return {};
    }
    auto victim = active.begin();

    std::uniform_int_distribution<int> rand(0, active.size() - 1);
    std::default_random_engine randGenerator;
    std::advance(victim, rand(randGenerator));

    auto pos         = victim->first;
    auto stealReqPtr = victim->second;

    // We remove the victim from active while we steal, so that if we suspend
    // no other thread gets in the way of our steal
    active.erase(pos);
    inactive[pos] = stealReqPtr;

    // Signal the thread that we need work from it and wait for some (or Nothing)
    std::get<0>(*stealReqPtr).store(true);
    auto resF = std::get<1>(*stealReqPtr).get();
    auto res = resF.get();

    // -1 depth signals that the thread we tried to steal from has finished it's search
    if (res && hpx::util::get<1>(*res) == -1) {
      return {};
    }

    // Allow this thread to be stolen from again
    active[pos] = stealReqPtr;
    inactive.erase(pos);
    return res;
  }
  HPX_DEFINE_COMPONENT_ACTION(SearchManager, getLocalWork);

  // Called by the scheduler to ask the searchManager to add more work
  // TODO: This should return a task type (or nullptr) like other schedulers
  bool getWork() {
    Response_t maybeStolen;
    if (active.empty()) {
      // No local threads running, steal distributed
      if (!distributedSearchManagers.empty()) {
        maybeStolen = tryDistributedSteal();
      } else {
        return false;
      }
    } else {
      maybeStolen = getLocalWork();
    }

    if (!maybeStolen) {
      // Couldn't schedule anything locally
      return false;
    } else {
      SearchInfo searchInfo      = hpx::util::get<0>(*maybeStolen);
      int depth                  = hpx::util::get<1>(*maybeStolen);
      hpx::naming::id_type prom  = hpx::util::get<2>(*maybeStolen);

      // Build the action
      auto shared_state = std::make_shared<SharedState_t>();
      auto nextId = activeIds.front();
      activeIds.pop();
      active[nextId] = shared_state;

      hpx::threads::executors::current_executor scheduler;
      scheduler.add(hpx::util::bind(FuncToCall::fn_ptr(), searchInfo, depth, shared_state, prom, nextId, this->get_id()));
      return true;
    }
  }
  HPX_DEFINE_COMPONENT_ACTION(SearchManager, getWork);

  // Action to allow work to be pushed eagerly to this searchManager
  void addWork(SearchInfo info, int depth, hpx::naming::id_type prom) {
    auto shared_state = std::make_shared<SharedState_t>();
    auto nextId = activeIds.front();
    activeIds.pop();
    active[nextId] = shared_state;

    hpx::threads::executors::current_executor scheduler;
    scheduler.add(hpx::util::bind(FuncToCall::fn_ptr(), info, depth, shared_state, prom, nextId, this->get_id()));
  }
  HPX_DEFINE_COMPONENT_ACTION(SearchManager, addWork);

  // Signal the searchManager that a local thread is now finished working and should be removed from active
  void done(unsigned activeId) {
    if (active.find(activeId) != active.end()) {
      active.erase(activeId);
    } else {
      // A steal must be in progress on this id so cancel it before finishing
      // Canceled steals (-1 flag) are already removed from active
      auto & state = inactive[activeId];
      std::get<1>(*state).set(hpx::util::make_tuple(SearchInfo(), -1, hpx::find_here()));
      inactive.erase(activeId);
    }
    activeIds.push(activeId);
  }
  HPX_DEFINE_COMPONENT_ACTION(SearchManager, done);
};

}

#define REGISTER_SEARCHMANAGER(searchInfo,Func)                                    \
  typedef workstealing::SearchManager<searchInfo, Func > __searchmgr_type_;        \
                                                                                   \
  HPX_REGISTER_ACTION(__searchmgr_type_::registerDistributedManagers_action,       \
                      BOOST_PP_CAT(__searchmgr_registerDistributedManagers_action, \
                                   BOOST_PP_CAT(searchInfo, Func)));               \
                                                                                   \
  HPX_REGISTER_ACTION(__searchmgr_type_::getWork_action,                           \
                      BOOST_PP_CAT(__searchmgr_getWork_action,                     \
                                   BOOST_PP_CAT(searchInfo, Func)));               \
                                                                                   \
  HPX_REGISTER_ACTION(__searchmgr_type_::addWork_action,                           \
                      BOOST_PP_CAT(__searchmgr_addWork_action,                     \
                                   BOOST_PP_CAT(searchInfo, Func)));               \
                                                                                   \
  HPX_REGISTER_ACTION(__searchmgr_type_::done_action,                              \
                      BOOST_PP_CAT(__searchmgr_done_action,                        \
                                   BOOST_PP_CAT(searchInfo, Func)));               \
                                                                                   \
  HPX_REGISTER_ACTION(__searchmgr_type_::getLocalWork_action,                      \
                      BOOST_PP_CAT(__searchmgr_getLocalWork_action,                \
                                   BOOST_PP_CAT(searchInfo, Func)));               \
                                                                                   \
  typedef ::hpx::components::component<__searchmgr_type_ >                         \
  BOOST_PP_CAT(__searchmgr_, BOOST_PP_CAT(searchInfo, Func));                      \
                                                                                   \
  HPX_REGISTER_COMPONENT(BOOST_PP_CAT(__searchmgr_,                                \
                                      BOOST_PP_CAT(searchInfo, Func)));            \

#endif
