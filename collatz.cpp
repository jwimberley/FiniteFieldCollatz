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
using coset = std::set<int>;
using cosets = std::set<coset>;

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

void print(std::ostream& os, const coset& c) {
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

void print (std::ostream& os, const cosets& cs) {
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

bool inClass(int k, const coset& c) {
  return	(c.count(k) == 1);
}

bool inClasses(int k, const cosets& cs) {
  for (const auto& c : cs) {
    if (inClass(k,c))
      return true;
  }
  return false;
}

cosets::iterator findClass(int k, const cosets& cs) {
  for (auto it = cs.begin(); it != cs.end(); ++it) {
    if (inClass(k,*it))
      return it;
  }
  return cs.end();
}

int findClassIndex(int k, const cosets& cs) {
  std::size_t i = 0;
  for (const auto& c : cs) {
    if (inClass(k,c))
      return i;
    ++i;
  }
  return -1;
}

coset getConjugacyClass(int p, int k0) {
  int k = k0;
  coset c;
  do {
    c.insert(k);
    k *= q;
    k %= p;
  } while (k != k0);
  return c;
}

cosets getConjugacyClasses(int p) {
  cosets cs;
  coset nc;
  nc.insert(0);
  cs.insert(nc);
  for (int k = 0; k < p; ++k) {
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

Graph getCosetGraph(int p, const cosets& cs) {
  std::vector< std::vector<bool> > adj_matrix(cs.size(),std::vector<bool>(cs.size(),false));
  auto universal = [&] (int row) {
    for (int col = 0; col < adj_matrix[row].size(); col++) {
      if (not adj_matrix[row][col])
	return false;
    }
    return true;
  };
  for (int k = 0; k < p; ++k) {
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

bool fakeCoset(int p, const coset& c) {
  for (int k : c) {
    if (k == 0) return true;
    if (gcd(k,p)>1) return true;
  }
  return false;
}

void printGraph(const Graph& g, int p, const cosets& cs, std::string name) {
  std::vector<std::string> vnames;
  std::vector<std::string> vcols;
  std::vector<std::string> vfills;
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
  }
  std::ofstream gfile(name);
  write_graphviz(gfile,g, make_my_label_writer(vnames,vcols,vfills));
}

void printGraph(const Graph& g, std::string name) {
  std::ofstream gfile(name);
  write_graphviz(gfile,g);
}

int graphInfo(const Graph& g, std::vector< std::vector<int> >& distanceMatrix, std::ostream& os = std::cout) {

  std::vector<int> component(num_vertices(g));
  int num = strong_components(g,make_iterator_property_map(component.begin(), get(vertex_index, g)));
  os << "Number of strongly connected components = " << num;
  if (num != 1) os << " -- not strongly connected!";
  os << std::endl;

  //std::vector<Vertex> parents(num_vertices(g));
  distanceMatrix.resize(num_vertices(g));
  for (auto& row : distanceMatrix)
    row.resize(num_vertices(g));
  std::vector<int> distances(num_vertices(g));
  os << "Dijkstra algorithm distances:" << std::endl;
  os << std::setw(8) << "";
  for (int v = 0; v < num_vertices(g); ++v) {
    os << std::setw(4) << v;
  }
  os << std::endl;
  os << std::setw(8) << "";
  for (int v = 0; v < num_vertices(g); ++v) {
    os << std::setw(4) << "----";
  }
  os << std::endl;
  for (int f = 0; f < num_vertices(g); ++f) {
    //dijkstra_shortest_paths(g,f,predecessor_map(&parents[0]).distance_map(&distances[0]));
    dijkstra_shortest_paths(g,f,distance_map(&distances[0]));
    os << std::setw(4) << f << " => ";
    for (int v = 0; v < num_vertices(g); ++v) {
      if (distances[v] == INT_MAX) {
	distances[v] = -1;
      }
      distanceMatrix[f][v] = distances[v];
      os << std::setw(4) << distances[v];
      //os << "parent(" << v << ") = " << parents[v] << std::endl;
    }
    os << std::endl;
  }
  os << std::endl;
  return num;
}

bool weakConjecture(int p, const cosets& cs, std::ostream& os = std::cout) {
  // if (cs.size() == 1) {
  //   os << "Only one cycle; trivial!" << std::endl;
  //   return true;
  // }
  Graph g = getCosetGraph(p,cs);
  std::vector< std::vector<int> > distanceMatrix;
  int num = graphInfo(g,distanceMatrix,os);
  bool subcon = false;
  if (p % a != 0) { // then should be strongly connected
    return (num == 1);
  } else { // just the non-fake cosets should be "strongly connected"
    std::vector<bool> good;
    for (const auto& c : cs) {
      if (fakeCoset(p,c))
	good.push_back(false);
      else
	good.push_back(true);
    }
    for (int f = 0; f < num_vertices(g); ++f) {
      for (int v = 0; v < num_vertices(g); ++v) {
	if (good[f] and good[v]) {
	  if (distanceMatrix[f][v] == -1)
	    return false;
	}
      }
    }
  }
  return true;
}

using namespace std;
int main(int argc, char *argv[]) {
  std::vector<int> tests = {15,17,31,40,81,6561,8233,32805};
  for (int p : tests) {
    if (p % q != 0) {
      cosets cs = getConjugacyClasses(p);
      Graph graph = getCosetGraph(p,cs);
      std::cout << "\n\n----- P = " << p << " -----\n";
      print(std::cout,cs);
      std::stringstream filename;
      filename << "graph" << p
	       << "_q" << q << "a" << a << "b" << b
	       << ".gv";
      printGraph(graph,p,cs,filename.str());
      weakConjecture(p,cs,std::cout);
    }
  }

  int N = 1000;
  std::vector<int> primes;
  for (int i = q+1; i < N; ++i)
    if (i % q != 0) primes.push_back(i);

  std::stringstream signature;
  signature << "q" << q << "a" << a << "b" << b << "_N" << N;
  std::string name = "collatz_output_";
  name += signature.str();
  name += ".txt";
  std::ofstream output(name);

  int exc = 0;
  for (int p : primes) {
    if (p % q == 0) continue;
    output << "\n\n----- P = " << p << " -----\n";
    cosets cs = getConjugacyClasses(p);
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
