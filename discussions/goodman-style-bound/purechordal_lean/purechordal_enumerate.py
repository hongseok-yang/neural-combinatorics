import itertools
import networkx as nx

def generate_all_graphs(n):
  """Generates all simple graphs on n vertices."""
  vertices = list(range(n))
  all_possible_edges = list(itertools.combinations(vertices, 2))
  graphs = []
  
  for num_edges in range(len(all_possible_edges) + 1):
    for edges in itertools.combinations(all_possible_edges, num_edges):
      G = nx.Graph()
      G.add_nodes_from(vertices)
      G.add_edges_from(edges)
      graphs.append(G)
      
  return graphs

def is_pure_chordal(G):
  """Checks if a graph is pure chordal (chordal with uniform maximal cliques >= 3)."""
  if not nx.is_chordal(G):
    return False
    
  maximal_cliques = list(nx.find_cliques(G))
  
  if not maximal_cliques:
    return False
    
  r = len(maximal_cliques[0])
  
  if r < 3:
    return False
    
  for clique in maximal_cliques:
    if len(clique) != r:
      return False
      
  return True

def filter_non_isomorphic(graphs):
  """Filters a list of graphs to keep only non-isomorphic ones."""
  unique_graphs = []
  for G in graphs:
    is_new = True
    for U in unique_graphs:
      if nx.is_isomorphic(G, U):
        is_new = False
        break
    if is_new:
      unique_graphs.append(G)
      
  return unique_graphs

def enumerate_pure_chordal_graphs(max_n):
  """Enumerates and prints all pure chordal graphs up to max_n vertices."""
  # We start at n=3 because r >= 3 requires at least 3 vertices.
  for n in range(3, max_n + 1):
    print(f"Checking n = {n}...")
    
    all_graphs = generate_all_graphs(n)
    pure_chordal = []
    
    for G in all_graphs:
      if is_pure_chordal(G):
        pure_chordal.append(G)
        
    unique_pure_chordal = filter_non_isomorphic(pure_chordal)
    
    print(f"Found {len(unique_pure_chordal)} non-isomorphic pure chordal graphs with {n} vertices.")
    for i, G in enumerate(unique_pure_chordal):
      print(f"  Graph {i + 1} edges: {list(G.edges())}")

if __name__ == "__main__":
  enumerate_pure_chordal_graphs(6)