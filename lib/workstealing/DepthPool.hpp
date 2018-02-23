#ifndef DEPTHPOOL_COMPONENT_HPP
#define DEPTHPOOL_COMPONENT_HPP

#include <queue>

#include <hpx/include/components.hpp>
#include <hpx/util/lockfree/deque.hpp>
#include <hpx/runtime/actions/basic_action.hpp>
#include <hpx/runtime/actions/component_action.hpp>
#include <hpx/util/function.hpp>
namespace hpx { namespace naming { struct id_type; } }

// #include "hpx/runtime/actions/transfer_action.hpp"               // for tran...
// #include "hpx/runtime/actions/transfer_continuation_action.hpp"  // for tran...
// #include "hpx/runtime/naming/name.hpp"                           // for intr...
// #include "hpx/runtime/serialization/serialize.hpp"               // for oper...
// #include "hpx/traits/is_action.hpp"                              // for is_a...
// #include "hpx/traits/needs_automatic_registration.hpp"           // for need...

namespace workstealing {

// A workqueue that tracks tasks based on the depth in the tree they were created at.
// This allows high vs low tasks to be distinguished while maintaining heuristics as much as possible.
// In particular a sequential user should see tasks in the same order as a sequential thread
// Currently only supports access by a single thread at a time as it's very non trivial to implement lock-free.
class DepthPool : public hpx::components::locking_hook<
  hpx::components::component_base<DepthPool>> {
 private:
  using fnType = hpx::util::function<void(hpx::naming::id_type)>;

  std::vector< std::queue<fnType> > pools;

  // For quicker access
  unsigned highest = 0;
  unsigned lowest = 0;

 public:
  fnType getLocal();
  HPX_DEFINE_COMPONENT_ACTION(DepthPool, getLocal);
  fnType steal();
  HPX_DEFINE_COMPONENT_ACTION(DepthPool, steal);
  void addWork(fnType task, unsigned depth);
  HPX_DEFINE_COMPONENT_ACTION(DepthPool, addWork);
};
}

HPX_REGISTER_ACTION_DECLARATION(workstealing::DepthPool::getLocal_action, DepthPool_getLocal_action);
HPX_REGISTER_ACTION_DECLARATION(workstealing::DepthPool::steal_action, DepthPool_steal_action);
HPX_REGISTER_ACTION_DECLARATION(workstealing::DepthPool::addWork_action, DepthPool_addWork_action);

#endif
