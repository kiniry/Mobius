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

public class GraphNode {

	private static int nextId=0;
	private final static int UNMARKED=Integer.MIN_VALUE;
	private final static int MinMARK =Integer.MIN_VALUE + 1 ;
	
	private int id; 							//introduces a natural ordering the class instances
	private int explorationMarker;
	
	private LinkedList outgoingEdges;			//should always be sorted
	private LinkedList incommingEdges;			//should always be sorted
	
	GraphNode(){
		id = nextId ;
		nextId ++;//System.err.println("incr node NextId");
		explorationMarker = UNMARKED;
		outgoingEdges = new LinkedList();
		incommingEdges= new LinkedList();
	}
	
	
	/* Adding Edges to the Node*/
	
	public void addAsIncommingTransition(OrientedEdge edge){ 
		//having a unique id Number is garantied by construction
		incommingEdges.add(edge);
		Collections.sort(incommingEdges);}
	public void addAsOutgoingTransition (OrientedEdge edge){  
		//having a unique id Number is garantied by construction
		outgoingEdges.add(edge);
		Collections.sort(outgoingEdges);}
	
	public void clear(){
		explorationMarker = UNMARKED;
		outgoingEdges = new LinkedList();
		incommingEdges= new LinkedList();
	}
	
	/* Managing exploration Markers */
	public void unmark(){  explorationMarker = UNMARKED; }
	public boolean setMarker(int i){ 
		if (i>= MinMARK) explorationMarker = i ;
		else return false;
		return true;
	}
	public boolean isUnmarked(){ return (explorationMarker==UNMARKED)? true : false ;}


	/**/
	public LinkedList getIncommingEdges(){return incommingEdges;}
	public LinkedList getOutgoingEdges() {return outgoingEdges; }	
	public int getIdentifier(){ return id;}	
	public int getMarker(){ return explorationMarker;}
	public int getId(){return id;}
	
	/* "implements" fucntions */
	public int compareTo(Object obj){
		
		int i;
		GraphNode node2;
		
		if(!(obj instanceof GraphNode)) throw new ClassCastException();
		node2=(GraphNode)obj;
		
		//returns 0 if the set of incomming Edges is identical
		return (id - node2.id);
	}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		GraphNode node = (GraphNode) super.clone();
		//System.err.println("cloning node "+node.id);
		node.id = nextId;//System.err.println("incr NextId (cloning node)");
		nextId++;
		return node;
	}
	public String toString(){
		return ""+id;
	}
		
}
