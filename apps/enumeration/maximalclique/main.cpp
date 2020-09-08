#include <iostream>
#include <numeric>
#include <algorithm>
#include <vector>
#include <map>
#include <chrono>
#include <memory>
#include <typeinfo>

#include <hpx/hpx_init.hpp>
#include <hpx/include/iostreams.hpp>

#include <boost/serialization/access.hpp>

#include "DimacsParser.hpp"
#include "BitGraph.hpp"
#include "BitSet.hpp"

#include "YewPar.hpp"

#include "skeletons/Seq.hpp"
#include "skeletons/DepthBounded.hpp"
#include "skeletons/StackStealing.hpp"
#include "skeletons/Ordered.hpp"
#include "skeletons/Budget.hpp"

#include "util/func.hpp"
#include "util/NodeGenerator.hpp"

// Number of Words to use in our bitset representation
// Possible to specify at compile to to handler bigger graphs if required
#ifndef NWORDS
#define NWORDS 8
#endif

template<unsigned n_words_>
auto orderGraphFromFile(const dimacs::GraphFromFile & g, std::map<int,int> & inv) -> BitGraph<n_words_> {
  std::vector<int> order(g.first);
  std::iota(order.begin(), order.end(), 0);

  // Order by degree, tie break on number
  std::vector<int> degrees;
  std::transform(order.begin(), order.end(), std::back_inserter(degrees),
                 [&] (int v) { return g.second.find(v)->second.size(); });

  std::sort(order.begin(), order.end(),
            [&] (int a, int b) { return ! (degrees[a] < degrees[b] || (degrees[a] == degrees[b] && a > b)); });


  // Construct a new graph with this new ordering
  BitGraph<n_words_> graph;
  graph.resize(g.first);

  for (unsigned i = 0 ; i < g.first ; ++i)
    for (unsigned j = 0 ; j < g.first ; ++j)
      if (g.second.find(order[i])->second.count(order[j]))
        graph.add_edge(i, j);

  // Create inv map (maybe just return order?)
  for (int i = 0; i < order.size(); i++) {
    inv[i] = order[i];
  }

  return graph;
}

template<unsigned n_words_>
auto colour_class_order(const BitGraph<n_words_> & graph,
                        const BitSet<n_words_> & p,
                        std::array<unsigned, n_words_ * bits_per_word> & p_order,
                        std::array<unsigned, n_words_ * bits_per_word> & p_bounds) -> void {
  BitSet<n_words_> p_left = p; // not coloured yet
  unsigned colour = 0;         // current colour
  unsigned i = 0;              // position in p_bounds

  // while we've things left to colour
  while (! p_left.empty()) {
    // next colour
    ++colour;
    // things that can still be given this colour
    BitSet<n_words_> q = p_left;

    // while we can still give something this colour
    while (! q.empty()) {
      // first thing we can colour
      int v = q.first_set_bit();
      p_left.unset(v);
      q.unset(v);

      // can't give anything adjacent to this the same colour
      graph.intersect_with_row_complement(v, q);

      // record in result
      p_bounds[i] = colour;
      p_order[i] = v;
      ++i;
    }
  }
}

// Main Maxclique B&B Functions
// Probably needs a copy constructor
struct MCSol {
  std::vector<int> members;
  int colours;

  template <class Archive>
  void serialize(Archive & ar, const unsigned int version) {
    ar & members;
    ar & colours;
  }
};

struct MCNode {
  friend class boost::serialization::access;

  MCSol sol;
  // int size;
  BitSet<NWORDS> remaining;
  BitSet<NWORDS> used;
  int leaf;

  int getObj() const {
    return leaf;
  }

  template <class Archive>
  void serialize(Archive & ar, const unsigned int version) {
    ar & sol;
    // ar & size;
    ar & remaining;
    ar & used;
    ar & leaf;
  }

};

struct GenNode : YewPar::NodeGenerator<MCNode, BitGraph<NWORDS> > {
  std::array<unsigned, NWORDS * bits_per_word> p_order;
  std::array<unsigned, NWORDS * bits_per_word> colourClass;

  std::reference_wrapper<const BitGraph<NWORDS> > graph;

  MCSol childSol;
  // int childBnd;
  BitSet<NWORDS> p,p1,p2,used_p;
  std::vector<BitSet<NWORDS>> used_f;
  int childLeaf;
  int v,v1;
  int length;
  bool flag;


  GenNode(const BitGraph<NWORDS> & graph, const MCNode & n) : graph(std::cref(graph)) {
    colour_class_order(graph, n.remaining, p_order, colourClass);
    childSol = n.sol;
    // childBnd = n.size+1;
    p = n.remaining;
    p1 = n.remaining;
    numChildren = p.popcount();
    v = numChildren - 1;
    v1 = numChildren -1;
    childLeaf = n.leaf;
    used_p = n.used;

    auto ca = p1;
    graph.intersect_with_row(p_order[v],ca);
    // p1.unset(p_order[v]);
    p2 = ca;


    // p1.set(p_order[v]);
    // if(n.sol.members.size()==0){
    //   for (size_t i = v; i >=0; i--)
    //   {
    //     auto can = p1;
    //     graph.intersect_with_row(p_order[v],can);
    //     used_f.push_back(can);
    //   }
      
    // }

  }

  // Get the next value
  MCNode next() override {
    auto sol = childSol;
    if(sol.members.size()==0 && p.popcount()==1){
      childLeaf = 2;
      sol.members.push_back(p_order[v]);
      auto cands = p;
     graph.get().intersect_with_row(p_order[v], cands);
      p.unset(p_order[v]);
      return {sol,cands,used_p,childLeaf};
    }
    sol.members.push_back(p_order[v]);
    sol.colours = colourClass[v] - 1;


    auto cands = p;
    graph.get().intersect_with_row(p_order[v], cands);

    // Side effectful function update
    p.unset(p_order[v]);

    // if(sol.members.size()==0){
    //   for (size_t i = v1; i > v; i--
    //   {
    //     if(used_f[i].)
    //   }
      
    // }


    if(sol.members.size()>1){

      if(!used_p.empty()){
        length = used_p.popcount();
        used_p.set(p_order[v]);
        if(length==used_p.popcount()){
          if(cands.empty()){
            childLeaf = 2;
          }
        }else{
          if(cands.empty()){
            childLeaf = 1;
          }else{
            used_p.set_all_zero();
          }
        }
    }

      if(v!=v1&&childLeaf==0){
        length = p2.popcount();
        p2.set(p_order[v]);
        if(length==p2.popcount()){
          if(cands.empty()){
            childLeaf = 2;
          }else{
            used_p = p2;
            // childLeaf = 3;
          }
          
        }else{
          if(cands.empty()){
            childLeaf = 1;
          }
        }
      }

      if(cands.empty()&&childLeaf==0){
        childLeaf = 1;
      }
    }
    v--;
    return {sol, cands, used_p, childLeaf};
  }

  // MCNode nth(unsigned n) {
  //   auto pos = v - n;

  //   auto sol = childSol;
  //   sol.members.push_back(p_order[pos]);
  //   sol.colours = colourClass[pos] - 1;

  //   auto cands = p;
  //   // Remove all choices from the left "left" of the one we care about
  //   for (auto i = v; i > pos; --i) {
  //     cands.unset(p_order[i]);
  //   }

  //   graph.get().intersect_with_row(p_order[pos], cands);

  //   return {sol, childBnd, cands};
  // }
};

struct CountSols : YewPar::Enumerator<MCNode, std::uint64_t>{
  std::uint64_t count = 0;
  std::vector<std::vector<int> > used;
  std::vector<int> a;
  size_t l;
  CountSols():count(0){};
  void accumulate(const MCNode & n) override{
    std::vector<int> flag;
    if(n.leaf==1){
      // count++;
      // for(auto i : n.sol.members){
      //   std::cout<<i+1<<" ";
      // }
      // std::cout<<std::endl;
      a = n.sol.members;
      if(used.size()==0){
        count++;
        used.push_back(a);
      }else{

        for(auto it : used){
          if(it.begin()!=a.begin()){
            for(auto i: a){
              if(!isContains(it,i)){
                flag.push_back(1);
                break;
              }
            }
          }

        }
        if(flag.size() == used.size()){
          count++;
          used.push_back(a);
        }
      }

    }
  }

  bool isContains(std::vector<int> a, int b){
    int l = a.size();
    for (size_t i = 0; i < l; ++i)
    {
      if(a[i]==b){
        return true;
      }
    }
    return false;
  }
  void combine(const std::uint64_t & other) override{
    count += other;
  }
  std::uint64_t get() override {return count;}
};

// int upperBound(const BitGraph<NWORDS> & space, const MCNode & n) {
//   return n.size + n.sol.colours;
// }


// typedef func<decltype(&upperBound), &upperBound> upperBound_func;


int hpx_main(boost::program_options::variables_map & opts) {
  /*
  if (!opts.count("input-file")) {
    std::cerr << "You must provide an DIMACS input file with \n";
    hpx::finalize();
    return EXIT_FAILURE;
  }
  */

  //boost::program_options::notify(opts);

  auto inputFile = opts["input-file"].as<std::string>();

  auto gFile = dimacs::read_dimacs(inputFile);

  // Order the graph (keep a hold of the map)
  std::map<int, int> invMap;
  auto graph = orderGraphFromFile<NWORDS>(gFile, invMap);

  auto spawnDepth = opts["spawn-depth"].as<std::uint64_t>();
  auto decisionBound = opts["decisionBound"].as<int>();

  auto start_time = std::chrono::steady_clock::now();

  // Initialise Root Node
  MCSol mcsol;
  mcsol.members.reserve(graph.size());
  mcsol.colours = 0;

  BitSet<NWORDS> cands, used;
  cands.resize(graph.size());
  cands.set_all();
  used.resize(graph.size());
  used.set_all_zero();
  MCNode root = { mcsol, cands, used, 0};

  auto sol = root;
  auto skeletonType = opts["skeleton"].as<std::string>();

  // auto size = opts["size"].as<unsigned>();
  // auto all = (1 << size) -1;
  std::uint64_t count;
  if (skeletonType == "seq") {
    YewPar::Skeletons::API::Params<> searchParameters;
    count = YewPar::Skeletons::Seq<GenNode,
                                    YewPar::Skeletons::API::Enumeration,
                                    YewPar::Skeletons::API::Enumerator<CountSols>,
                                    YewPar::Skeletons::API::DepthLimited>
            ::search(graph,root,searchParameters);
  } else if (skeletonType == "depthbounded") {
    YewPar::Skeletons::API::Params<> searchParameters;
    searchParameters.spawnDepth = spawnDepth;
    count = YewPar::Skeletons::DepthBounded<GenNode,
                                            YewPar::Skeletons::API::Enumeration,
                                            YewPar::Skeletons::API::Enumerator<CountSols>,
                                            YewPar::Skeletons::API::DepthLimited>
            ::search(graph,root,searchParameters);
  } else if (skeletonType == "stacksteal") {
    YewPar::Skeletons::API::Params<> searchParameters;
    searchParameters.stealAll = static_cast<bool>(opts.count("chunked"));
    count = YewPar::Skeletons::StackStealing<GenNode,
                                            YewPar::Skeletons::API::Enumeration,
                                            YewPar::Skeletons::API::Enumerator<CountSols>,
                                            YewPar::Skeletons::API::DepthLimited>
          ::search(graph,root,searchParameters);
  } else if (skeletonType == "budget") {
    YewPar::Skeletons::API::Params<> searchParameters;
    searchParameters.backtrackBudget = opts["backtrack-budget"].as<unsigned>();
    count = YewPar::Skeletons::Budget<GenNode,
                                            YewPar::Skeletons::API::Enumeration,
                                            YewPar::Skeletons::API::Enumerator<CountSols>,
                                            YewPar::Skeletons::API::DepthLimited>
          ::search(graph,root,searchParameters);
  } else {
    hpx::cout << "Invalid skeleton type option. Should be: seq, depthbound, stacksteal" << hpx::endl;
    hpx::finalize();
    return EXIT_FAILURE;
  }

  auto overall_time = std::chrono::duration_cast<std::chrono::milliseconds>
    (std::chrono::steady_clock::now() - start_time);

  hpx::cout << "MaximalClique Count = " << count << hpx::endl;
  hpx::cout << "cpu = " << overall_time.count() << hpx::endl;

  return hpx::finalize();
}

int main (int argc, char* argv[]) {
  boost::program_options::options_description
    desc_commandline("Usage: " HPX_APPLICATION_STRING " [options]");

  desc_commandline.add_options()
    ( "skeleton",
      boost::program_options::value<std::string>()->default_value("seq"),
      "Which skeleton to use: seq, depthbound, stacksteal, budget, or ordered"
      )
    ( "spawn-depth,d",
      boost::program_options::value<std::uint64_t>()->default_value(0),
      "Depth in the tree to spawn at"
      )
    ( "backtrack-budget,b",
      boost::program_options::value<unsigned>()->default_value(50),
      "Number of backtracks before spawning work"
      )
    ( "input-file,f",
      boost::program_options::value<std::string>()->required(),
      "DIMACS formatted input graph"
      )
    ("discrepancyOrder", "Use discrepancy order for the ordered skeleton")
    ("chunked", "Use chunking with stack stealing")
    ("poolType",
     boost::program_options::value<std::string>()->default_value("depthpool"),
     "Pool type for depthbounded skeleton")
    ( "decisionBound",
    boost::program_options::value<int>()->default_value(0),
    "For Decision Skeletons. Size of the clique to search for"
    );

  YewPar::registerPerformanceCounters();

  return hpx::init(desc_commandline, argc, argv);
}
