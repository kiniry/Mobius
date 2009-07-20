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
public class OrientedEdge implements Comparable, Cloneable{

	private static int nextId=0;
	private final static int UNMARKED=Integer.MIN_VALUE;
	private final static int MinMARK =Integer.MIN_VALUE + 1 ;
	
	private int id; 
	private GraphNode incommingNode;
	private GraphNode outgoingNode;
	
	private int explorationMarker;

	
	OrientedEdge(){
		id = nextId;
		nextId ++; //System.err.println("incr edge NextId");
		incommingNode= new GraphNode();
		outgoingNode = new GraphNode();
		explorationMarker = UNMARKED;
	}
	
	public void setIncommingNode(GraphNode incomming){incommingNode = incomming;}
	public void setOutgoingNode(GraphNode outgoing){outgoingNode = outgoing;}
	public void clear(){
		incommingNode= new GraphNode();
		outgoingNode = new GraphNode();
		explorationMarker = UNMARKED;
	}
	
	/* marker management */
	public void unmark(){  explorationMarker = UNMARKED; }
	public boolean setMarker(int i){ 
		if (i>= MinMARK) explorationMarker = i ;
		else return false;
		return true;
	}
	public boolean isUnmarked(){ return (explorationMarker==UNMARKED)? true : false ;}	
	
	
	/* Accessors */
	public GraphNode getIncommingNode(){return incommingNode;}
	public GraphNode getOutgoingNode() {return outgoingNode ;}
	public int getIdentifier(){ return id;}	
	public int getMarker(){ return explorationMarker;}	
	public int getId(){return id;}
	
	
	/* "implements" fucntions */
	public int compareTo(Object obj){
		
		int i;
		OrientedEdge edge2;
		
		if (! (obj instanceof OrientedEdge)) throw new ClassCastException();
		edge2 = (OrientedEdge) obj;
		
		// returns 0 if the Edges points toward the sames elements
		return (this.id - edge2.id) ;
			
	}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		OrientedEdge edge = (OrientedEdge) super.clone();
		//System.err.println("cloning edge "+edge.id);
		edge.id = nextId;
		nextId ++;//System.err.println("incr NextId (cloning edge)");
		return edge;
	}
	public String toString(){
		return ""+id;
	}
}
