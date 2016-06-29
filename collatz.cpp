#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <vector>
#include <set>
#include <climits>

#include <boost/config.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include <boost/graph/strong_components.hpp>
#include <boost/graph/graphviz.hpp>

using namespace boost;
using Edge = std::pair<int,int>;
using Graph = adjacency_list<vecS, vecS, bidirectionalS, no_property, property < edge_weight_t, int > >;
using Vertex = graph_traits<Graph>::vertex_descriptor;

template <class Name>
class my_label_writer {
public:
  my_label_writer(Name _name, Name _col, Name _fill) : name(_name), col(_col), fill(_fill) {}
  template <class VertexOrEdge>
  void operator()(std::ostream& out, const VertexOrEdge& v) const {
    out << "[label=\"" << name[v]
	<< "\", color=\"" << col[v]
	<< "\", bgcolor=\"" << fill[v]
	<< "\"]";
  }
private:
  Name name;
  Name col;
  Name fill;
};

template <class Name>
my_label_writer<Name>
make_my_label_writer(Name n, Name c, Name f) {
  return my_label_writer<Name>(n, c, f);
}

const bool useNullClass = false;

const int q = 2;
const int a = 3;
const int b = 1;

int gcd(int a, int b) {
  int x;
  while (b) {
    x = a % b;
    a = b;
    b = x;
  }
  return a;
}

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
    k *= q;
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
  int kmin = (useNullClass) ? 0 : 1;
  for (int k = kmin; k < p; ++k) {
    //if (gcd(k,p)>1) continue;
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
      edges.push_back(Edge(row,row-1));
      weights.push_back(1);
    } else {
      edges.push_back(Edge(row,row));
      weights.push_back(1);
    }
  }
  if (connected)
    edges.push_back(Edge(3,1));
  else
    edges.push_back(Edge(1,3));
  weights.push_back(1);
  Graph graph(edges.begin(),edges.end(),weights.begin(),N);
  return graph;
}

Graph getCosetGraph(int p, const conjclasses& cs) {
  std::vector< std::vector<bool> > adj_matrix(cs.size(),std::vector<bool>(cs.size(),false));
  auto universal = [&] (int row) {
    for (int col = 0; col < adj_matrix[row].size(); col++) {
      if (not adj_matrix[row][col])
	return false;
    }
    return true;
  };
  int kmin = (useNullClass) ? 0 : 1;
  for (int k = kmin; k < p; ++k) {
    //if (gcd(k,p)>1) continue;
    int i = findClassIndex(k,cs);
    if (i < 0 or universal(i))
      continue;
    int kp = (a*k+b) % p;
    int j = findClassIndex(kp,cs);
    if (j >= 0)
      adj_matrix[i][j] = true;
  }
	
  std::vector<Edge> edges;
  std::vector<int> weights;
  for (int row = 0; row < adj_matrix.size(); ++row) {
    for (int col = 0; col < adj_matrix[row].size(); col++) {
      if (adj_matrix[row][col]) {
	edges.push_back(Edge(row,col));
	weights.push_back(1);
      }
    }
  }
  Graph graph(edges.begin(),edges.end(),weights.begin(),cs.size());
  return graph;
}

bool fakeCoset(int p, const conjclass& c) {
  for (int k : c) {
    if (k == 0) return true;
    if (gcd(k,p)>1) return true;
  }
  return false;
}

void printGraph(const Graph& g, int p, const conjclasses& cs, std::string name) {
  std::vector<std::string> vnames;
  std::vector<std::string> vcols;
  std::vector<std::string> vfills;
  std::cout << __LINE__ << std::endl;
  for (const auto& c : cs) {
    if (fakeCoset(p,c)) {
      vcols.push_back("red");
      vfills.push_back("red");
    } else {
      vcols.push_back("black");
      vfills.push_back("lightgrey");
    }
    std::stringstream vn;
    int count = 0;
    for (int k : c) {
      if (count > 0) vn << ",";
      vn << k;
      if (count > 2) {
	vn << ",...";
	break;
      }
      ++count;
    }
    vnames.push_back(vn.str());
    std::cout << vn.str() << std::endl;
  }
  std::cout << __LINE__ << std::endl;
  std::ofstream gfile(name);
  write_graphviz(gfile,g, make_my_label_writer(vnames,vcols,vfills));
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
  std::vector<int> component(num_vertices(g));
  int num = strong_components(g,make_iterator_property_map(component.begin(), get(vertex_index, g)));
  os << "Number of strongly connected components = " << num;
  if (num != 1) os << " -- not strongly connected!";
  os << std::endl;
  return allgood;
}

bool weakConjecture(int p, const conjclasses& cs, std::ostream& os = std::cout) {
  if (cs.size() == 1) {
    os << "Only one cycle; trivial!" << std::endl;
    return true;
  }
  Graph g = getCosetGraph(p,cs);
  return weakConjecture(g,os);
}

using namespace std;
int main(int argc, char *argv[]) {
  std::vector<int> tests = {15,17,40,6561,8233,32805};
  for (int p : tests) {
    if (p % q != 0) {
      conjclasses cs = getConjugacyClasses(p);
      Graph graph = getCosetGraph(p,cs);
      std::cout << "\n\n----- P = " << p << " -----\n";
      print(std::cout,cs);
      std::stringstream filename;
      filename << "graph" << p
	       << "_q" << q << "a" << a << "b" << b
	       << ".gv";
      printGraph(graph,p,cs,filename.str());
      weakConjecture(graph,std::cout);
    }
  }

  int N = 1000;
  std::vector<int> primes;
  for (int i = q+1; i < N; ++i)
    if (i % q != 0) primes.push_back(i);

  std::string name = "collatz_output";
  if (useNullClass) name += "_null";	
  name += ".txt";
  std::ofstream output(name);

  int exc = 0;
  for (int p : primes) {
    if (p % q == 0) continue;
    output << "\n\n----- P = " << p << " -----\n";
    conjclasses cs = getConjugacyClasses(p);
    print(output,cs);
    bool good = weakConjecture(p,cs,output);
    if (not good) {
      ++exc;
      std::cout << "P = " << p << " fails!" << std::endl;
      output << "P = " << p << " fails!" << std::endl;
    }
  }
  std::cout << "Done! There are " << exc << " exceptions out of " << primes.size() << " primes." << std::endl;
}
