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



/* a simple path is by definition a path using at most once each edge*/
public class SimplePath implements Comparable , Cloneable{

	
	protected LinkedList path; //linkedList of transition linking the from GraphNode to the to GraphNode
	
	protected OrientedGraph graph;
	protected LinkedList nodes;	//contains all the GraphNodes used by the path (always sorted)
	protected LinkedList edges;	//contains all the GraphNodes used by the path (always sorted)

	protected boolean hasCycle;
	
	public int attachedValue;
	
	SimplePath(OrientedGraph g){

		path = new LinkedList();
		
		graph = g;
		nodes = new LinkedList();
		edges = new LinkedList();
				
		hasCycle = false;
		
	}
	
	
	/* Modification functions */
	public boolean addHeadPath(SimplePath initPath){
		return addHeadPath(initPath.path);}
	public boolean addQueuPath(SimplePath initPath){
		return addQueuPath(initPath.path);}
	public boolean addHeadPath(LinkedList initPath){
		// Complexity in O(initPath.size())
		int j = initPath.size();
		boolean b;
		for(int i=0 ; i<j ; i++){
			if (! addHead((OrientedEdge)initPath.get(i))) {
				this.clear();
				return false;
			};
		}
		
		return true;
	}
	public boolean addQueuPath(LinkedList initPath){
		// Complexity in O(initPath.size())
		int j = initPath.size();
		boolean b;
		for(int i=0 ; i<j ; i++){
			if (! addQueue((OrientedEdge)initPath.get(i))) {
				this.clear();
				return false;
			};
		}
		
		return true;
	}
	public boolean addHead(OrientedEdge edge){
		return addPosition(edge, 0);
	};
	public boolean addQueue(OrientedEdge edge){
		return addPosition(edge,edges.size());
	};
	protected boolean addPosition(OrientedEdge edge, int pos){
		//add a transition at the given position in the path
		//  and remains all lists sorted, the insertion shifts from the pos'th element
		//  (included) and place the given edge a the pos'th position in the path 
		
		//System.err.println("adding edge at position "+pos);
		
		int i=edgePosition(edge);
		GraphNode node1,node2;
		
		//avoid position inconsitancy
		if (edges.size()<pos || (pos<0)) return false;
		
		if (edges.size()==0) {
			path.add(edge);
			edges.add(edge);
			node1 = edge.getIncommingNode();
			node2 = edge.getOutgoingNode();
			nodes.add(edge.getIncommingNode());
			i=nodePosition(node2);
			if (i==0) hasCycle = true ;
			else nodes.add(nodePosition(node2),node2); //constant time
			return true;
		}
		
		//avoid inserting twice an edge : it is the property of SINGLE path
		if(i<edges.size()) //in the case an element has to be added as queue element
			if (((OrientedEdge)edges.get(i)).compareTo(edge)==0) return false;

		//avoid inserting an inconsistent element in the path at postion pos
		if (pos != edges.size()) { //if it is not inserted as the last element
			if (edge.getOutgoingNode().compareTo(((OrientedEdge)path.get(pos)).getIncommingNode())!=0) return false;
		}
		if (pos != 0){
			if (edge.getIncommingNode().compareTo(((OrientedEdge)path.get(pos-1)).getOutgoingNode())!=0) return false;
		}

		//System.err.println("check successful, add operation is being performed");
			
		path.add(pos,edge);
		edges.add(i,edge);	
		node1 = edge.getIncommingNode();
		node2 = edge.getOutgoingNode();
		//nodes.add(edge.getIncommingNode());
		
		if (pos==0){
			i=nodePosition(node1);
			if (i<nodes.size()){
				if (((GraphNode)nodes.get(i)).compareTo(node1) !=0) nodes.add(i,node1);
				else hasCycle=true; //comes back to an already visited node
			}else{nodes.add(i,node2);} //node doesn't exist and should be inserted
		}
		if (pos==path.size()-1){
			i=nodePosition(node2);
			if (i<nodes.size()){
				if (((GraphNode)nodes.get(i)).compareTo(node2) !=0) nodes.add(i,node2);
				else hasCycle=true; //comes back to an already visited node
			}else{nodes.add(i,node2);} //node doesn't exist and should be inserted
		}
		
		//System.err.println("add operation performed");
		
		return true;	
	}
	public void clear(){
		path.clear();
		edges.clear();
		nodes.clear();
		hasCycle = false;
	}
	public int size(){
		return path.size();}

	
	
	/* Get information on Path*/
	public boolean isCircuit(){ 
		GraphNode from, to;
		from = getFrom();
		to = getTo();
		return (from.compareTo(to)==0)? true : false; };
	public boolean contains(GraphNode node){
		//execution in log(N)
		int i = nodePosition(node);
		int j = nodes.size();
		if (i>=j) return false;
		return (((GraphNode)nodes.get(i)).compareTo(node)==0);
	}
	public boolean contains(OrientedEdge edge){
		//execution in log(N)
		int i = edgePosition(edge);
		int j = edges.size();
		if (i>=j) return false;
		return (((OrientedEdge)edges.get(i)).compareTo(edge)==0);
	}
	private int nodePosition(GraphNode node){
		//function return the position of node in the nodes list;
		//in case the element doesn't belong to the list, it returns
		// the position would have to be inserted
		
		// execution in O(log2(N)) with N the number of nodes in the path
		
		GraphNode tmpNode;
		boolean found = false;
		int max = nodes.size() - 1;	//if list is void max<0
		int min = 0;
		int i=0; 

		//edges.get(min) & edges.get(max) are allowed values
		//min and max are converging toward the position of i
		while (min<=max && !found){
			i = ((max+min)-(max+min)%2)/2; 	//floor
			//System.err.println("curpos="+i);			
			tmpNode = (GraphNode) nodes.get(i);
			int j = node.compareTo(tmpNode);
			if (j==0) found = true;
			else{
				if( j > 0) min = i+1;
				else max = i-1 ;
			}	
			//System.err.println("sign="+j);
			//System.err.println("min="+min);
			//System.err.println("max="+max);
		}
		if(!found){i = (min>i)? i+1 : i ;}
		return i;
	}
	private int edgePosition(OrientedEdge edge){
		//function return the position of edge in the nodes list;
		//in case the element doesn't belong to the list, it returns
		// the position would have to be inserted
		
		// execution in O(log2(N)) with N the number of nodes in the path
		
		OrientedEdge tmpEdge;
		boolean found = false;
		int max = edges.size() - 1;	//if list is void max<0
		int min = 0;
		int i=0; 

		//edges.get(min) & edges.get(max) are allowed values
		//min and max are converging toward the position of i
		while (min<=max && !found){
			i = ((max+min)-(max + min)%2)/2; 	//floor
			//System.err.println("max="+max);
			//System.err.println("min="+min);
			//System.err.println("i="+i);
			tmpEdge = (OrientedEdge) edges.get(i);
			int j = edge.compareTo(tmpEdge);
			if (j==0) found = true;
			else{
				if( j > 0) min = i+1;
				else max = i-1 ;
			}	
		}
		if(!found){i = (min>i)? i+1 : i ;}
		return i;
	}
	public GraphNode findConnectionWith(SimplePath secPath){
		GraphNode node;
		if (this.size()>secPath.size())	{
			for(int i=secPath.size() ; i>0 ; i--){
				node = (GraphNode) secPath.nodes.get(i-1);
				if (this.contains(node)) return node;}
		}
		else{
			for(int i=this.size() ; i>0 ; i--){
				node = (GraphNode) this.nodes.get(i-1);
				if (secPath.contains(node)) return node;}
		}
		
		return new GraphNode();
	}
	
	
	
	
	
	
	
	/*public SimplePath extractSubPath(GraphNode from, GraphNode to){
		
		LinkedList subPath= new LinkedList();
		
		
		
		return new SimplePath(graph,subPath);
	}*/
	
	
	/* Implement interfaces*/
	public int compareTo(Object obj){
		
		int i,k,m;
		LinkedList path2;
		OrientedEdge edge1, edge2;
		
		if(!(obj instanceof SimplePath)) throw new ClassCastException();
		path2=((SimplePath)obj).getPath();
		m = path.size();
		k = path2.size();
		for( int j= 0 ; j<k && j<m ; j++){
			edge1 = (OrientedEdge) path.get(j);
			edge2 = (OrientedEdge) path2.get(j);
			i = edge1.compareTo(edge2);
			if (i!=0) return i;
		}
		//if 2 path have been the same, consider length
		// obvisouly if there length is the same, the path are the same
		// otherwise the shortest will be sorted first
		return (m-k);
	}
	protected Object clone() throws CloneNotSupportedException
	{ 
		return super.clone();
	}
	public String toString(){
		String string = "";

		if (path.size()==0) return "Path is void";
		
		GraphNode from, to;
		from = ((OrientedEdge) path.getFirst()).getIncommingNode();
		to = ((OrientedEdge) path.getLast()).getOutgoingNode();
		string = to.getIdentifier()+"";
		for(int i=path.size() ; i>0 ; i--) { 
			string = ((OrientedEdge) path.get(i-1)).getIncommingNode().getIdentifier()+"-> "+string;}
		string = " Path leading from "+from.getIdentifier()+" to "+to.getIdentifier()+"\n\t["+string+"]\n";	
		return string;
	}
	
	
	/* Direct Accessors */
	public LinkedList getPath(){return path;}
	public GraphNode getFrom() {return ((OrientedEdge)path.getFirst()).getIncommingNode();}
	public GraphNode getTo(){return ((OrientedEdge) path.getLast()).getOutgoingNode();}
	public OrientedEdge getEdge(int i){
		if (i<0 && i>path.size()) return null;
		return (OrientedEdge) path.get(i);
	}
	public LinkedList getAllGraphNodes(){return nodes;}

	
	
	/* Private utility functions */
	public void unmarkAllNodes(){
		for(int i=nodes.size() ; i>0 ; i--) {((GraphNode)nodes.get(i-1)).unmark();}
	}
	public void unmarkAllEdges(){
		for(int i=edges.size() ; i>0 ; i--) {((OrientedEdge)edges.get(i-1)).unmark();}
	}
	
	
}

