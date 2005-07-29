/*
 * Created on May 19, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author tdupont
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

import java.util.*;

public class OrientedGraph {

	public LinkedList nodes; 	//keep it ordered
	public LinkedList edges;	//keep it ordered
	private GraphNode init;
	
	OrientedGraph(){
		nodes = new LinkedList();
		edges = new LinkedList();
		init  = null;
	}
	
	
	/* Functions modifying the Graph*/
	
	protected void setInitialNode(GraphNode init){this.init = init;}
	
	public LinkedList addNodes(LinkedList nodeList){
		//should return the list of elements for with insertion failed
		
		LinkedList returnList = new LinkedList();
		GraphNode node;
		//System.err.println("Node List is: "+nodeList);
		for(int i=nodeList.size() ; i > 0; i--) {
			node = (GraphNode) nodeList.get(i-1);
			if (! addSingleNode(node)) returnList.add(node);
		}
		//System.err.println("Inserted Node List is: "+nodes);
		return returnList;
	}
	public LinkedList addEdges(LinkedList edgeList){
		//should return the list of elements for with insertion failed
		
		LinkedList returnList = new LinkedList();
		OrientedEdge edge;
		//System.err.println("edge List is: "+edgeList);
		for(int i=edgeList.size() ; i > 0; i--) {
			edge = (OrientedEdge) edgeList.get(i-1);
			if (! addSingleEdge(edge)) returnList.add(edge);
		}
		//System.err.println("Inserted edge List is: "+edges);
		return returnList;
	}
	public boolean addSingleNode(GraphNode node){
		//Adds one edge to the list of edges
		
		//presupposes that nodes list is ordered,
		// add element in log2(n), return true if succeed 
		// return false if failed (the only reason would be that the element is already in the list)
		// list remains sorted at the end
		GraphNode tmpNode;
		
		boolean found = false;
		int max = nodes.size() - 1;	//if list is void max<0
		int min = 0;
		int i = 0; //Trick to remove initial case (see below)

		//edges.get(min) & edges.get(max) are allowed values
		//min and max are converging toward the position of i
		while (min<=max && !found){
			i = ((max+min)-(max + min)%2)/2; //floor
			tmpNode = (GraphNode) nodes.get(i);
			int j = node.compareTo(tmpNode);
			if (j==0) found = true;
			else{
				if( j > 0) min = i+1;
				else max = i-1 ;
			}	
		}
		
		//Adds the edge if the element is not already in the list
		if(! found){
			/*  i, min, max gives an idea where edge should be inserted
			 	min > i => expected to be the element right after i   (1)
			 	max < i => expected to be the element right before i	(2)  
			 	cases (1)^(2) are disjoint
				if edges is void, max=-1 ; min = 0 => i=0 */
			
			i = (min>i)? i+1 : i ;
			nodes.add(i,node);
		}	
		return found;
	}
	public boolean addSingleEdge(OrientedEdge edge){
		//Adds one edge to the list of edges
		
		//presupposes that edges list is ordered,
		// add element in log2(n), return true if succeed 
		// return false if failed (the only reason would be that the element is already in the list)
		// list remains sorted at the end
		OrientedEdge tmpEdge;
		
		boolean found = false;
		int max = edges.size() - 1;	//if list is void max<0
		int min = 0;
		int i = 0; //Trick to remove initial case (see below)

		//edges.get(min) & edges.get(max) are allowed values
		//min and max are converging toward the position of i
		while (min<=max && !found){
			i = ((max+min)-(max + min)%2)/2; //floor
			tmpEdge = (OrientedEdge) edges.get(i);
			int j = edge.compareTo(tmpEdge);
			if (j==0) found = true;
			else{
				if( j > 0) min = i+1;
				else max = i-1 ;
			}	
		}
		
		//Adds the edge if the element is not already in the list
		if(! found){
			/*  i, min, max gives an idea where edge should be inserted
			 	min > i => expected to be the element right after the ith element  (1)
			 	max < i => expected to be the element right before the ith element (2)  
			 	cases (1)^(2) are disjoint
				Init : if edges is void, max=-1 ; min = 0 => i=0 */
			
			i = (min>i)? i+1 : i ; //insertion at ith position appends right before the current ith element 
			edges.add(i,edge);
		}	
		return found;
	}
	public void clear(){
		nodes = new LinkedList();
		edges = new LinkedList();
		init  = null;
	}

	
	/** This function returns all simple circuit possible **/
	public LinkedList findAllSimpleCircuit(){
		
		/*	Algo 
		 * 	(simplified version provided only for understanding, valid if 1 edge has only one successor
		 * 		=> introduces at most one new cycle) 
		 * 
		 * 
		Init : 	Zero transitions treated
				Create a void Graphe g
				g.addNodes(nodes);
				SimplePath singlePath ;				
		
		Invariant : g has no Cycles ; cycles contains all the single cycle possible to find
			// Basic idea is that one Edge introduces a maximum of 1 new cycle	
			//   let j be the number of cycles	
		for(int i=0 ; i<edges.size() ; i++):
				edge = (OrientedEdge) edges.get(i);										
				singlePath = new SimplePath(S, new LinkedList);							
				if pathSearch(edge.outgoingNode, edge.incommingNode, singlePath)		 
					singlePath.addHead(edge);											
					assert singlePath.isCycle()==true;									
					cycles.add(singlePath)												 
				else
					g.addSingleEdge(edge)												
		
		Ending : All transitions of the Graphe are processed 
		         All simple cycles have been extracted */
		

		LinkedList cycles = new LinkedList();
		OrientedEdge edge ;
		SimplePath path = new SimplePath(this);
		SimpleCircuit circuit;	
		OrientedEdge finalEdge;
		LinkedList tmpList;
		boolean hasCycle=false;
		
		//System.err.println("searching circuits");
		
		//mark all edges
		for(int i=edges.size() ; i>0 ; i-- ) ((OrientedEdge) edges.get(i-1)).setMarker(0); //O(N)
		
		for(int i = edges.size() ; i>0 ; i--){
			edge = (OrientedEdge) edges.get(i-1);
			//System.err.println("Current edge id="+edge.getId()+")");
			
			//adding an edge, may add as many circuits as there are outgoing edges to the node edge.getOutgoingNode()
			//for each unmarked edge depending of the  of the node edge.getIncommingNode()
			tmpList = edge.getIncommingNode().getIncommingEdges();
			for (int j=tmpList.size() ; j>0 ; j--){
				finalEdge = (OrientedEdge) tmpList.get(j-1);

				if (finalEdge.isUnmarked()){ //if this edge has been already 'added' to the graph
					unmarkAllNodes();
					path.clear();
					//System.err.println(edge.getOutgoingNode()+"- - >"+finalEdge.getIncommingNode());
					if (elementaryPathSearch(edge.getOutgoingNode(), finalEdge.getIncommingNode(), path)){
						//edge creates a cycle, it is virtually not added to the possible path in graph
						path.addHead(edge);
						path.addHead(finalEdge);
						//System.err.println("Adding following cycle"+path.getPath());
						if ( ! path.isCircuit()) System.err.println("Error in extracting cycles from graph, check algorithm");
						else {
							circuit = new SimpleCircuit(this,path);
							cycles.add(circuit);
							hasCycle = true;
						}
					}
				}
			}
			
			if (hasCycle==false) {
				edge.unmark(); //edge is virtually added to the graph
				//System.err.println("edge added (id="+edge.getId()+")");
			} 
			else hasCycle = false;
		}
				
		//System.err.println("All cycles have been found presumably");
		
		return cycles;
	}
	public LinkedList findAllSimplePath(GraphNode from, GraphNode to){
		
		/*	First find one path
		 * 	Out of this path find alternative paths if any by preventing the use of the same transitions
		 */
		LinkedList pathList = new LinkedList();
		LinkedList tmpPathList = new LinkedList();
		Iterator it;
		GraphNode tmpNode;
		OrientedEdge edge;		
		SimplePath alternativePath = new SimplePath(this);
		SimplePath mainPath = new SimplePath(this);
		SimplePath queu = new SimplePath(this);
		
		unmarkAllEdges();
		if (! elementaryPathSearch(from, to, mainPath)) return pathList; // in < O(N) ; see note below
		pathList.add(mainPath);
		
		System.err.println("main path found: "+mainPath);
				
		//path may be void (if from and to are the same)
		for (int i=mainPath.size() ; i>0 ; i--){ //in M*   ; M=nbEdges in Path found
			
			edge = (OrientedEdge) mainPath.getEdge(i-1); // equivalent to removeLast()
			
			//remove the last edge from the possible edges
			edge.setMarker(1); //random marker != UNMARKED
			
			
			//Search if there is any alternative Path
			tmpNode = edge.getOutgoingNode();
			alternativePath.clear();
			if ( elementaryPathSearch(from, tmpNode, alternativePath)){ //in <O(N) ; if one considers the amount of transition
																		//              per node as constant
				//recursive Call
				tmpPathList = findAllSimplePath(from , to);
				//add last part of the path to reach the to destination (given in parameter)
				for (int j=pathList.size() ; j<0 ; i++){				//in O(P) ; P number of path
					alternativePath = (SimplePath) pathList.get(i-1);
					alternativePath.addQueuPath(queu);
				}
				//tmpPathList now is a list of Path linked to the final target
				pathList.addAll(tmpPathList);
				
				//pathList has been updated with the list of new paths
			}
			
			//complementary path contains the part of the givenPath already explored
			queu.addHead(edge);
			
		}
		
		return pathList;
				
		//there are Sum(P) recursive call
		// algo in Sum(P)*(N+(M*(N+P))
		// M is maximised by N (the longest path)
		// ==> algo in O(Sum(P).(N.N + N.P))
		
	}
	
	
	/* an elementary path  use at most each node once 
	   a single path would use at most each edge once*/
	public boolean elementaryPathSearch(GraphNode start, GraphNode end, SimplePath path){
		
		if (start.compareTo(end)==0) { 
			//System.err.println("No need to search, start=end");
			return true;} //executed only once at start up
													//by def a node is always reachable from himself
		else {
			//System.err.println("search path "+start+"- - >"+end);
			return recursivePathSearch(start, end, path);
		}
	}
	private boolean recursivePathSearch(GraphNode start, GraphNode end, SimplePath path){
		
		/*	Performs a search on the oriented graph among all unmarked edges and unmarked nodes
	 	the algorithm modifies nodes' marks
	 	
	 		Operates in O(N) , with N the total number of unmarked nodes in the graph 
	 	*/		
		
		OrientedEdge edge;
		
		start.setMarker(1); 
		//System.err.println("current node is:"+start+" ("+end+")");
		
		for(int i=start.getOutgoingEdges().size() ; i>0 ; i--){

			edge = (OrientedEdge) start.getOutgoingEdges().get(i-1);
			if (edge.isUnmarked()){
				if(edge.getOutgoingNode().compareTo(end)==0) {
					//if goal is reached
					path.addHead(edge);
					return true;
				}
				
				if (edge.getOutgoingNode().isUnmarked()){
	
					//if destination node has not been explored yet and edge can be exploit
					if (recursivePathSearch(edge.getOutgoingNode(), end, path) ) {
						path.addHead(edge);
						//System.err.println("return true: "+path);
						return true;
					}
				}	
			}
		}		
		//System.err.println("returning false");
		return false;
	}
	
	
	
	/* Private utility functions */
	private void unmarkAllNodes(){
		for(int i=nodes.size() ; i>0 ; i--) {((GraphNode)nodes.get(i-1)).unmark();}
	}
	private void unmarkAllEdges(){
		for(int i=edges.size() ; i>0 ; i--) {((OrientedEdge)edges.get(i-1)).unmark();}
	}
	
}
