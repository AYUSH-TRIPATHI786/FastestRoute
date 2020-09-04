import java.util.Scanner;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.PriorityQueue;

public class FriendSuggestion {
    private static class Impl {
        // Number of nodes
        // int n;
        // adj[0] and cost[0] store the initial graph, adj[1] and cost[1] store the reversed graph.
        // Each graph is stored as array of adjacency lists for each node. adj stores the edges,
        // and cost stores their costs.
        ArrayList<Integer>[][] adj;
        ArrayList<Integer>[][] cost;
        // distance[0] and distance[1] correspond to distance estimates in the forward and backward searches.
        Long[][] distance;
        // Two priority queues, one for forward and one for backward search.
        ArrayList<PriorityQueue<Entry>> queue;
        // visited[v] == true iff v was visited either by forward or backward search.
        boolean[][] visited;
        // List of all the nodes which were visited either by forward or backward search.
        ArrayList<Integer> workset;
        final Long INFINITY = Long.MAX_VALUE / 4;

        Impl(int n) {
            //this.n = n;
            visited = new boolean[2][n];
            Arrays.fill (visited[0], false);
            Arrays.fill(visited[1], false);
            workset = new ArrayList<Integer>();
            distance = new Long[][] {new Long[n], new Long[n]};
            for (int i = 0; i < n; ++i) {
                distance[0][i] = distance[1][i] = INFINITY;
            }
            queue = new ArrayList<PriorityQueue<Entry>>();
            queue.add(new PriorityQueue<Entry>(n));
            queue.add(new PriorityQueue<Entry>(n));
        }

        // Reinitialize the data structures before new query after the previous query
        void clear() {
            for (int v : workset) {
                distance[0][v] = distance[1][v] = INFINITY;
                visited[0][v] = false;
                visited[1][v] = false;
            }
            workset.clear();
            queue.get(0).clear();
            queue.get(1).clear();
        }

        //v Try to relax the distance in direction side(0 for forward and 1 for backward) from source to node v using value dist.
        void visit(int side, int u, Long dist) {
            // Implement this method yourself
        	for(int i=0 ; i<adj[side][u].size() ; i++) {
        		int v = adj[side][u].get(i);
        		int w = cost[side][u].get(i);
        		if(distance[side][v] > dist + w) {
        			distance[side][v] = dist + w;
        			queue.get(side).add(new Entry(distance[side][v],v));
        			workset.add(v);
        		}
        	}
        }
        
        
        long shortestPath(long sd) {
        	for(int i = 0 ; i < workset.size() ; i++) {
        		int v = workset.get(i);
        		if (sd > distance[0][v] + distance[1][v] ) {
        			sd = distance[0][v] + distance[1][v];
        		}
        	}
        	return sd;
        }

        // Returns the distance from s to t in the graph.
        Long query(int s, int t) {
        	if(s==t)
        		return 0L;
            // Reinitialize the data structures before new query after the previous query
            clear();
            //Try to relax the distance in direction forward from s to s using value 0.
            visit(0, s, 0L);
            distance[0][s] = 0L;
            visited[0][s] = true;
            workset.add(s);
            visit(1, t, 0L);
            distance[1][t]=0L;
            visited[1][t]=true;
            workset.add(t);
            do {
                // s and t are not connected
            	if(queue.get(0).isEmpty()) {
            		return -1L;
            	}
            	
            	//node with the shortest distance in the forward queue
            	int u = queue.get(0).poll().node;
            	
            	if(visited[1][u]==true) {
            		return shortestPath(distance[0][u] + distance[1][u]);//since it is not necessary that shortest path is through u 
            	}else if(visited[0][u] == false) {
            		visit(0,u,distance[0][u]);
            		visited[0][u] = true;    		
            		
            	}
            	
            	// s and t are not connected
            	if(queue.get(1).isEmpty()) {
            		return -1L;
            	}
            	
            	//node with the shortest distance in the backward queue
            	u = queue.get(1).poll().node;
            	
            	if(visited[0][u]==true) {
            		return shortestPath(distance[0][u] + distance[1][u]);//since it is not necessary that shortest path is through u 
            	}else if(visited[1][u] == false) {
            		visit(1,u,distance[1][u]);
            		visited[1][u] = true;
            	}
            }while(true);
        }
   
        class Entry implements Comparable<Entry> 
        {
            Long cost;
            int node;
          
            public Entry(Long cost, int node)
            {
                this.cost = cost;
                this.node = node;
            }
         
            public int compareTo(Entry other)//now least priority is at head
            {
                return cost < other.cost ? -1 : cost > other.cost ? 1 : 0;
            }
        }
    }
    
    @SuppressWarnings("unchecked")
    public static void main(String args[]) {
        Scanner in = new Scanner(System.in);
        int n = in.nextInt();
        int m = in.nextInt();
        Impl BiDij = new Impl(n);
        BiDij.adj = (ArrayList<Integer>[][])new ArrayList[2][];
        BiDij.cost = (ArrayList<Integer>[][])new ArrayList[2][];
        for (int side = 0; side < 2; ++side) {
            BiDij.adj[side] = (ArrayList<Integer>[])new ArrayList[n];
            BiDij.cost[side] = (ArrayList<Integer>[])new ArrayList[n];
            for (int i = 0; i < n; i++) {
                BiDij.adj[side][i] = new ArrayList<Integer>();
                BiDij.cost[side][i] = new ArrayList<Integer>();
            }
        }


        for (int i = 0; i < m; i++) {
            int x, y, c;
            x = in.nextInt();
            y = in.nextInt();
            c = in.nextInt();
            BiDij.adj[0][x - 1].add(y - 1);
            BiDij.cost[0][x - 1].add(c);
            BiDij.adj[1][y - 1].add(x - 1);
            BiDij.cost[1][y - 1].add(c);
        }

        int t = in.nextInt();

        for (int i = 0; i < t; i++) {
            int u, v;
            u = in.nextInt();
            v = in.nextInt();
            System.out.println(BiDij.query(u-1, v-1));
           
        }in.close();
        }
}
