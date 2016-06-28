#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>
#include <set>
#include <climits>

#include <boost/config.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include <boost/graph/graphviz.hpp>

using namespace boost;
using Edge = std::pair<int,int>;
using Graph = adjacency_list<vecS, vecS, bidirectionalS, no_property, property < edge_weight_t, int > >;
using Vertex = graph_traits<Graph>::vertex_descriptor;

const bool useNullClass = false;
const bool useWeakConj = true;
const bool useSuperStrongConj = false;
const bool usePrimePowers = true;

std::vector<int> getPrimesUnder(int N) {
  std::vector<int> seeds = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97};
  std::vector<bool> isprime(N+1,true);
  isprime[0] = false;
  isprime[1] = false;
  for (int k = 2; k <= 100; ++k)
    isprime[k] = false;
  for (int p : seeds)
    isprime[p] = true;
  int max = sqrt(N);
  for (int k = 2; k <= max; ++k) {
    if (isprime[k]) {
      for (int l = k*k; l <= N; l += k) {
	isprime[l] = false;
      }
    }
  }
  for (int k = 100; k <= N; ++k) {
    if (isprime[k])
      seeds.push_back(k);
  }
  return seeds;
}

std::vector<int> getPrimePowersUnder(int N) {
  std::vector<int> pows = getPrimesUnder(N);
  std::size_t orig = pows.size();
  for (std::size_t k = 0; k < orig; ++k) {
    int p0 = pows[k];
    int p = p0;
    while ((p *= p0) < N and p > 0) {
      pows.push_back(p);
    }
  }
  std::sort(pows.begin(),pows.end());
  return pows;
}

using conjclass = std::set<int>;
using conjclasses = std::set<conjclass>;
using cycle = std::vector<conjclasses::iterator>;

void print(std::ostream& os, const conjclass& c) {
  os << "{";
  int count = 0;
  for (int k : c) {
    if (count > 0)
      os << ", ";
    os << k;
    if (count > 5) {
      os << "...";
      break;
    }
    ++count;
  }
  os << "}";
}

void print (std::ostream& os, const conjclasses& cs) {
  os << "{" << std::endl;
  int k = 0;
  for (const auto& c : cs) {
    os << "\t" << k << ": ";
    print(os,c);
    os << std::endl;
    ++k;
  }
  os << "}" << std::endl;
}

bool inClass(int k, const conjclass& c) {
  return	(c.count(k) == 1);
}

bool inClasses(int k, const conjclasses& cs) {
  for (const auto& c : cs) {
    if (inClass(k,c))
      return true;
  }
  return false;
}

conjclasses::iterator findClass(int k, const conjclasses& cs) {
  for (auto it = cs.begin(); it != cs.end(); ++it) {
    if (inClass(k,*it))
      return it;
  }
  return cs.end();
}

int findClassIndex(int k, const conjclasses& cs) {
  std::size_t i = 0;
  for (const auto& c : cs) {
    if (inClass(k,c))
      return i;
    ++i;
  }
  return -1;
}

conjclass getConjugacyClass(int p, int k0) {
  int k = k0;
  conjclass c;
  do {
    c.insert(k);
    k *= 2;
    k %= p;
  } while (k != k0);
  return c;
}

conjclasses getConjugacyClasses(int p) {
  conjclasses cs;
  if (useNullClass) {
    conjclass nc;
    nc.insert(0);
    cs.insert(nc);
  }
  for (int k = 1; k < p; ++k) {
    if (not inClasses(k,cs))
      cs.insert(getConjugacyClass(p,k));
  }
  return cs;
}

Graph getTestGraph(bool connected) {
  int N = 5;
  std::vector<Edge> edges;
  std::vector<int> weights;
  for (int row = 0; row < N; ++row) {
    if (row != 3 and row != 0) {
      edges.push_back(Edge(row-1,row));
      weights.push_back(1);
    } else {
      edges.push_back(Edge(row,row));
      weights.push_back(1);
    }
  }
  if (connected)
    edges.push_back(Edge(1,3));
  else
    edges.push_back(Edge(3,1));
  weights.push_back(1);
  Graph graph(edges.begin(),edges.end(),weights.begin(),N);
  return graph;
}

Graph getFieldGraph(int p, const conjclasses& cs) {
  std::vector< std::vector<bool> > adj_matrix(cs.size(),std::vector<bool>(cs.size(),false));
  auto universal = [&] (int row) {
    for (int col = 0; col < adj_matrix[row].size(); col++) {
      if (not adj_matrix[row][col])
	return false;
    }
    return true;
  };
  for (int k = 1; k < p; ++k) {
    int i = findClassIndex(k,cs);
    if (i < 0 or universal(i))
      continue;
    int kp = (3*k+1) % p;
    int j = findClassIndex(kp,cs);
    if (j >= 0)
      adj_matrix[i][j] = true;
  }
	
  std::vector<Edge> edges;
  std::vector<int> weights;
  for (int row = 0; row < adj_matrix.size(); ++row) {
    for (int col = 0; col < adj_matrix[row].size(); col++) {
      if (adj_matrix[row][col])
	//edges.push_back(Edge(row,col));
	edges.push_back(Edge(col,row));
      weights.push_back(1);
    }
  }
  Graph graph(edges.begin(),edges.end(),weights.begin(),cs.size());
  return graph;
}

void printGraph(const Graph& g, std::string name) {
  std::ofstream gfile(name);
  write_graphviz(gfile,g);
}

bool weakConjecture(const Graph& g, std::ostream& os = std::cout) {
  Vertex id = vertex(0,g);
  std::vector<Vertex> parents(num_vertices(g));
  std::vector<int> distances(num_vertices(g));
  dijkstra_shortest_paths(g,id,predecessor_map(&parents[0]).distance_map(&distances[0]));
  bool allgood = true;
  for (int v = 0; v < num_vertices(g); ++v) {
    if (distances[v] == INT_MAX) {
      allgood = false;
      distances[v] = -1;
    }
    os << "distance(" << v << ") = " << distances[v] << ", ";
    os << "parent(" << v << ") = " << parents[v] << std::endl;
  }
  os << std::endl;
  return allgood;
}

bool weakConjecture(int p, const conjclasses& cs, std::ostream& os = std::cout) {
  if (cs.size() == 1) {
    os << "Only one cycle; trivial!" << std::endl;
    return true;
  }
  Graph g = getFieldGraph(p,cs);
  return weakConjecture(g,os);
}

bool fullCycle(const cycle& cy, const conjclasses& cs) {
  conjclass nc;
  nc.insert(0);
  for (auto it = cs.begin(); it != cs.end(); ++it) {
    if (useNullClass) {
      if (*it == nc)
	continue;
    }
    if (std::find(cy.begin(),cy.end(),it) == cy.end()) {
      return false;
    }
  }
  return true;
}

bool superstrongConjecture(int p, const conjclasses& cs, std::ostream& os = std::cout) {
  if (cs.size() == 1) {
    os << "Only one cycle; trivial!" << std::endl;
    return true;
  }
  conjclasses::iterator it1 = findClass(1,cs);
  std::vector<bool> cache(p,false);
  for (int k = 2; k < p; ++k) {
    if (cache[k] == false) {
      if (not inClass(k,*it1)) {
	std::vector<int> v;
	cycle cy;
	std::vector<int> i;
	int kp = k;
	do {
	  cy.push_back(findClass(kp,cs));
	  i.push_back(findClassIndex(kp,cs));
	  v.push_back(kp);
	  cache[kp] = true;
	  kp = (3*kp+1) % p;
	  //} while (findClass(kp,cs) != findClass(k,cs));
	} while (kp != k);				
	bool full = fullCycle(cy,cs);
	if (full) {
	  os << "Cycle found!" << std::endl;
	  for (int z : v)
	    os << z << ", ";
	  os << std::endl;
	  os << "(";
	  for (int z : i)
	    os << z << ", ";
	  os << ")\n";
	  return true;
	}
      }
    }
  }
  os << "No cycle found!" << std::endl;
  return false;
}

bool strongConjecture(int p, const conjclasses& cs, std::ostream& os = std::cout) {
  if (cs.size() == 1) {
    os << "Only one cycle; trivial!" << std::endl;
    return true;
  }
  int identity = findClassIndex(1,cs);
  std::vector<bool> badcache(p,false);
  std::vector<bool> goodcache(p,false);
  std::vector<bool> connected(cs.size(),false);
  connected[identity] = true;
  int ck = 0;
  int sizecount = 0;
  for (const auto& c : cs) {
    if (connected[ck]) {
      ++ck;
      continue;
    }
    bool found = false;
    for (int k : c) {
      if ((not badcache[k]) and (not goodcache[k])) {
	std::vector<int> v;
	std::vector<int> i;
	int ii;
	int kp = k;
	do {
	  if (goodcache[kp]) {
	    found = true;
	    break;
	  }
	  if (badcache[kp]) {
	    found = false;
	    break;
	  }
	  ii = findClassIndex(kp,cs);
	  v.push_back(kp);
	  i.push_back(ii);
	  if (ii == identity) {
	    found = true;
	    break;
	  }
	  kp = (3*kp+1) % p;
	} while (kp != k);				
	if (found) {
	  int count = 0;
	  for (int z : v) {
	    goodcache[k] = true;
	    if (count > 0) {
	      os << ", ";
	    }
	    os << z;
	    if (count > 5)
	      break;
	    ++count;
	  }
	  if (v.size() > 5) os << "...";
	  os << ")\t (";
	  count = 0;
	  for (int z : i) {
	    if (z >= 0)
	      connected[z] = true;
	    if (count > 0) {
	      os << ", ";
	    }
	    os << z;
	    if (count > 5)
	      break;
	    ++count;
	  }
	  if (i.size() > 5) os << "...";
	  os << ")\t -- size = " << i.size() << "\n";
	  sizecount += i.size()-1;
	} else {
	  for (int z : v)
	    badcache[k] = true;
	}
      }
      if (found)
	break;
    }
    ++ck;
  }
  bool allc = true;
  for (int i = 0; i < cs.size(); ++i) {
    if (not connected[i]) {
      os << "Coset " << i << " not connected!" << std::endl;
      allc = false;
    }
  }
  os << "Total cycle size = " << sizecount << std::endl;
  return allc;
}


using namespace std;
int main(int argc, char *argv[]) {
  conjclasses cs8233 = getConjugacyClasses(8233);
  Graph graph8233 = getFieldGraph(8233,cs8233);
  printGraph(graph8233,"graph8233.gv");
	
  conjclasses cs6561 = getConjugacyClasses(6561);
  Graph graph6561 = getFieldGraph(6561,cs6561);
  printGraph(graph6561,"graph6561.gv");

  Graph test = getTestGraph(false);
  printGraph(test,"testgraph.gv");
  weakConjecture(test,std::cout);
		
  int N = 500000;
  std::vector<int> primes = (usePrimePowers) ? getPrimePowersUnder(N) : getPrimesUnder(N);
  std::string name = "collatz_output";
  if (useWeakConj) name += "_weak";
  if (useSuperStrongConj) name += "_ss";
  if (usePrimePowers) name += "_pows";
  if (useNullClass) name += "_null";	
  name += ".txt";
  std::ofstream output(name);

  int exc = 0;
  for (int p : primes) {
    if (p % 2 == 0) continue;
    output << "\n\n----- P = " << p << " -----\n";
    conjclasses cs = getConjugacyClasses(p);
    print(output,cs);
    bool good;
    if (useWeakConj)
      good = weakConjecture(p,cs,output);
    else if (useSuperStrongConj)
      good = superstrongConjecture(p,cs,output);
    else
      good = strongConjecture(p,cs,output);
    if (not good) {
      ++exc;
      std::cout << "P = " << p << " fails!" << std::endl;
      output << "P = " << p << " fails!" << std::endl;
    }
  }
  std::cout << "Done! There are " << exc << " exceptions out of " << primes.size() << " primes." << std::endl;
}
