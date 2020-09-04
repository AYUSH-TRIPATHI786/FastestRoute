import java.util.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.PriorityQueue;
import static java.lang.Math.*;

public class DistPreprocessSmall {
    private static class Impl {
    	
        int n;
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
        boolean[] contracted ;
        ArrayList<Shortcut> qS = new ArrayList<Shortcut>();//used to store the shortcuts that that has to be created in order to contract node v
        ArrayList<Integer> cover = new ArrayList<Integer>();//used to store the covers/nodes to/from which a shortcut has to be made while contracting a node         
        
        long[] dist;
        
        // Position of the node in the node ordering
        Integer[] rank;
        
        //Importance criteria of contraction of nodes
        // Level of the node for level heuristic in the node ordering
        Long[] level;
        //No. of contracted neighbors
        long[] cn;
        //Edge difference before and after contracting
        long[] ed;
        //shortest cover //no. of node to make a shortcut to or from
        long[] sc;
        
        //constructor
        Impl(int n) {
            this.n = n;
            visited = new boolean[2][n];
            Arrays.fill (visited[0], false);
            Arrays.fill(visited[1], false);
            workset = new ArrayList<Integer>();
            rank = new Integer[n];
            level = new Long[n];
            cn = new long[n];
            ed = new long[n];
            sc = new long[n];
            
            distance = new Long[][] {new Long[n], new Long[n]};
            for (int i = 0; i < n; ++i) {
                distance[0][i] = distance[1][i] = INFINITY;
                level[i] = 0L;
                rank[i] = 0;
            }
            queue = new ArrayList<PriorityQueue<Entry>>();
            queue.add(new PriorityQueue<Entry>(n));
            queue.add(new PriorityQueue<Entry>(n));
        }
        
        
        class Entry implements Comparable<Entry>
        {
            Long cost;//distance from source in query and importance in preprocessing
            int node;
          
            public Entry(Long cost, int node)
            {
                this.cost = cost;
                this.node = node;
            }
         
            public int compareTo(Entry other)
            {
                if (cost == other.cost) {
                    return node < other.node ? -1 : node > other.node ? 1: 0;
                }
                return cost < other.cost ? -1 : cost > other.cost ? 1 : 0;
            }
        }
        
        class Shortcut
        {
            int u;
            int v;
            Long cost;

            public Shortcut(int u, int v, Long c)
            {
                this.u = u;
                this.v = v;
                cost = c;
            }
        }

        // Preprocess the graph
        void preprocess() {
            // This priority queue will contain pairs (importance, node) with the least important node in the head
            PriorityQueue<Entry> q = new PriorityQueue<Entry>(n);            
            contracted = new boolean[n];// keeps track of contracted nodes
            dist = new long[n];
            for( int i=0 ; i<n ; i++) {
            	q.add(new Entry(0L,i));
            }
            int i = 0;
            while(!q.isEmpty()) {
            	Entry e = q.poll();
            	int v = e.node;
            	e.cost = shortcut(v);//getting the importance of v
            	if(q.isEmpty() || e.cost <= q.peek().cost) {//will execute this after importance of all the nodes is calculated
            		rank[v] = i ;
            		i++ ;
            		contract(v) ;
            		contracted[v] = true ;
            	}else {//will execute this untill importance of all the nodes is calculated
            		q.add(e);
            		qS.clear();
            	}
            }
            
        }
         
        //now actually contracting node v //not pseudo
        void contract(int v) {
            
            //add the shortcuts that we found while executing shortcut(v)
        	while(!qS.isEmpty()) {
        		apply_shortcut(qS.remove(0));
        	}
            
            //updating cn and level values of predecessors of v 
            for(int i = 0 ; i < adj[1][v].size() ; i++) {
        		int u = adj[1][v].get(i);
        		if(contracted[u]==false) {
        			cn[u]++;
        			level[u] = max(level[u],level[v]+1);
        		}
        	}
            //updating cn and level values of successors of v 
        	for(int j = 0 ; j<adj[0][v].size() ; j++) {
    			int w = adj[0][v].get(j);
    			if(contracted[w]==false){
    				cn[w]++;
    				level[w] = max(level[w],level[v]+1);
    			}
        	}
        }
        
        void clearPre() {
            for (int v : workset) {
                dist[v] =  INFINITY;
            }
            workset.clear();
        }
        
        //adding edge after contracting a node
        void add_edge(int side, int u, int v, Long c) {
            //checking if an edge from u to v already exists
            for (int i = 0; i < adj[side][u].size(); ++i) {
                int w = adj[side][u].get(i);
                if (w == v) {
                    Long cc = min(cost[side][u].get(i), c);
                    cost[side][u].set(i, cc);
                    return;
                }
            }
            adj[side][u].add(v);
            cost[side][u].add(c);
        }
        
        //adding edges/shortcut after contracting a node
        void apply_shortcut(Shortcut sc) {
            add_edge(0, sc.u, sc.v, sc.cost);
            add_edge(1, sc.v, sc.u, sc.cost);
        }
    

        // Add the shortcuts corresponding to contracting node v. Return v's importance.
        Long shortcut (int v) {
            //pseudo contraction to find importance
        	long l1 = 0;
        	long l2 = 0;
            
        	for(int i = 0 ; i < adj[1][v].size() ; i++) {
        		int u = adj[1][v].get(i);//predecessor
        		l2 = cost[1][v].get(i );
        		if(contracted[u]==false) {
        			for(int j = 0 ; j<adj[0][v].size() ; j++) {
        				int w = adj[0][v].get(j);//successor
    					l1 = cost[0][v].get(j);
        				if(contracted[w]==false) {	
        					dijkstraPseudo(u,w,l1,l2,v); //finding a shortest path or will make a shortcut //not actually
        				}
        			}
        		}	
        	}
            // Computing the node importance in the end
            Long shortcuts = 0L;
            Long vlevel = 0L;
            Long neighbors = 0L;
            Long shortcutCover = 0L;
            vlevel = level[v];
            neighbors = cn[v];
            shortcuts = (long)qS.size();
            shortcutCover = (long)cover.size();
            cover.clear();
            
            Long importance = 4*vlevel + 2*neighbors + shortcuts + shortcutCover;
            return importance;
        }
        
        //used just in finding the importance of a node in shortcut function
        void dijkstraPseudo(int s,int t,long l1, long l2,int v) {
        	PriorityQueue<Entry> q = new PriorityQueue<Entry>();
        	clearPre();
        	dist[s] = 0;
        	q.add(new Entry(0L , s));
        	while(true) {
        			int u = q.poll().node;
                    
                    
        			if(dist[u]>(l1+l2)) {
                        //all other points at a distance more than l1 + l2 so add shortcut
        				qS.add(new Shortcut(s,t,l1+l2));
                        //a shortcut is made from s so add it as in the list of cover of v
        				if(!cover.contains(s)) {
        					cover.add(s);
        				}
                        //a shortcut is made to t so add it as in the list of cover of v
        				if(!cover.contains(t)) {
        					cover.add(t);
        				}
        				// when a shortcut is about to made
        				return;
        			}
                    
                    //no need of making shortcut since we found a shortest path
        			if(u == t) {
        				return;
        			}
                    
                    //continue finding shortest path
        			for(int i=0 ; i<adj[0][u].size(); i++) {
        				int w = adj[0][u].get(i);
                		long length = cost[0][u].get(i);
                		if (w != v && contracted[w]==false) {
                			if (dist[w] > dist[u] + length) {
                				dist[w] = dist[u] + length;
                				workset.add(w);
                				q.add(new Entry(dist[w],w));
                			}
                		}	
        			}
                    
                    if(q.isEmpty()) {
        			    //we cannot reach from s to t without crossing through v so make shortcut while contracting v
                        qS.add(new Shortcut(s,t,l1+l2));
        				if(!cover.contains(s)) {
        					cover.add(s);
        				}
        				if(!cover.contains(t)) {
        					cover.add(t);
        				}
        				return;
        			}
        	}
        }
        
        // Returns the shortest distance from s to t in the graph
        Long query(int s, int t) {
             if (s == t) {
                return 0L;
            }
            clear();
            visit(0, s, 0L);
            visit(1, t, 0L);
            mark_visited(0,s);
            mark_visited(1,t);
            distance[0][s] = 0L;
            distance[1][t]=0L;
            workset.add(t);
            workset.add(s);
            Long estimate = INFINITY;
            
            //Using bidirectional dijkstra towards only towards most important node
            while(!queue.get(0).isEmpty() || !queue.get(1).isEmpty()) {
            	
                //forward search
                if(!queue.get(0).isEmpty()) {
            		Entry e = queue.get(0).poll();
            		int u = e.node;
            		if ( e.cost <= estimate) {
            			visit(0,u,e.cost);
            			mark_visited(0,u);
            		}
            		if ( visited[1][u]==true && distance[0][u]+distance[1][u] < estimate) {
            			estimate = distance[0][u]+distance[1][u];
            		}
            	}
                
                //backward search
            	if(!queue.get(1).isEmpty()) {
            		//System.out.println("backward");
            		Entry e = queue.get(1).poll();
            		int u = e.node;
            		//System.out.println(rank[u]);
            		if ( e.cost <= estimate) {
            			visit(1,u,e.cost);
            			mark_visited(1,u);
            		}
            		if ( visited[0][u]==true && distance[0][u]+distance[1][u] < estimate) {
            			estimate = distance[0][u]+distance[1][u];
            		}
            	}
            }
            return estimate == INFINITY ? -1 : estimate;            
        }
                // See the description of this method in the starter for friend_suggestion
        boolean visit(int side, int u, Long dist) {
            // Implement this method yourself
        	for(int i=0 ; i<adj[side][u].size() ; i++) {
        		int v = adj[side][u].get(i);
        		if(rank[v] > rank[u] ) { //Move towards the most important node
        			long w = cost[side][u].get(i);
        			if(distance[side][v] > dist + w) {
        				distance[side][v] = dist + w;
        				queue.get(side).add(new Entry(distance[side][v],v));
        				workset.add(v);
        			}
       			}
        	}
        	return false;
        } 
        
        void mark_visited(int side, int u) {
            visited[side][u] = true;     
        }
        
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
    }

    public static void main(String args[]) {
        Scanner in = new Scanner(System.in);
        int n = in.nextInt();
        int m = in.nextInt();
        Impl ch = new Impl(n); 
        @SuppressWarnings("unchecked")
        ArrayList<Integer>[][] tmp1 = (ArrayList<Integer>[][])new ArrayList[2][];
        ch.adj = tmp1;
        @SuppressWarnings("unchecked")
        ArrayList<Long>[][] tmp2 = (ArrayList<Long>[][])new ArrayList[2][];
        ch.cost = tmp2;
        for (int side = 0; side < 2; ++side) {
            @SuppressWarnings("unchecked")
            ArrayList<Integer>[] tmp3 = (ArrayList<Integer>[])new ArrayList[n];
            ch.adj[side] = tmp3;
            @SuppressWarnings("unchecked")
            ArrayList<Long>[] tmp4 = (ArrayList<Long>[])new ArrayList[n];
            ch.cost[side] = tmp4;
            for (int i = 0; i < n; i++) {
                ch.adj[side][i] = new ArrayList<Integer>();
                ch.cost[side][i] = new ArrayList<Long>();
            }
        }

        for (int i = 0; i < m; i++) {
            int x, y;
            Long c;
            x = in.nextInt();
            y = in.nextInt();
            c = in.nextLong();
            ch.adj[0][x - 1].add(y - 1);
            ch.cost[0][x - 1].add(c);
            ch.adj[1][y - 1].add(x - 1);
            ch.cost[1][y - 1].add(c);
        }

        ch.preprocess();
        System.out.println("Ready");

        int t = in.nextInt();

        for (int i = 0; i < t; i++) {
            int u, v;
            u = in.nextInt();
            v = in.nextInt();
            System.out.println(ch.query(u-1, v-1));
        }
    }
}
