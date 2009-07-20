/*
 * Created on May 24, 2005
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

public class SimpleCircuit extends SimplePath{
	
	public int anyNumber;  	// this field in unused by any function of the class
							//its only purpose is to be able to attach a number to the instance from outside the instance

	SimpleCircuit(OrientedGraph g, LinkedList initPath){
		super(g);
		anyNumber = 0 ;
	}
	SimpleCircuit(OrientedGraph g, SimplePath initPath){
		super(g);
		anyNumber = 0 ;
		initCircuit(initPath);
	}
	SimpleCircuit(OrientedGraph g){
		super(g);
		anyNumber = 0 ;
	}
	
	//add single element
	public boolean addHead(OrientedEdge edge){return false;} //compulsary redefinition
	public boolean addQueue(OrientedEdge edge){return false;}//mandatory  redefinition
	public boolean addPosition(OrientedEdge edge, int pos){
		//make it possible to insert an edge that doesn't modify the circuit nature
		if ( (pos==0) ||(pos==edges.size()) ) return false;
		return super.addPosition(edge, pos);
	}
	public boolean addHeadPath(LinkedList initPath){return false;}
	public boolean addQueuPath(LinkedList initPath){return false;}

	
	public GraphNode findInnerConnectionWith(SimplePath secPath){
		//This methods does the same as findConnectionWith but excludes the border of
		//  the path form the search;
		
		
		GraphNode node;
		GraphNode avoidInit = ((OrientedEdge)secPath.getPath().getFirst()).getIncommingNode(); 
		GraphNode avoidEnd  = ((OrientedEdge)secPath.getPath().getLast() ).getOutgoingNode();
		
		System.err.println("lists are:");
		System.err.println("path: "+secPath);
		for(int i=0; i<secPath.nodes.size(); i++){System.err.println(secPath.nodes.get(i));}
		System.err.println("cycle: "+this);
		for(int i=0; i<this.nodes.size(); i++){System.err.println(this.nodes.get(i));}
		
		if (secPath.getClass().getName().compareTo(this.getClass().getName())==0)
			System.err.println("Using this method with cycles as parameter is risky !");
			
		for(int i=secPath.nodes.size()-1 ; i>1 ; i--){
			node = (GraphNode) secPath.nodes.get(i-1);
			if (this.contains(node)) {
				if (node.compareTo(avoidInit)!=0 && node.compareTo(avoidEnd)!=0)
				{ System.err.println("Both lists contain "+node);return node;}
			}
			else System.err.println("cycle doesn't contain node "+node.getId());
			
		}
		
		System.err.println("retourne brecouille");
		return new GraphNode();
	}	

	
	
	//initialise circuit
	public boolean initCircuit(LinkedList initPath){
		boolean b=super.addHeadPath(initPath);
		if (b==true) return initCircuit(this);
		return false;
	}
	public boolean initCircuit(SimplePath initPath){
		hasCycle = initPath.isCircuit();
		if (!hasCycle && initPath==this){ 			
			super.clear();	//has been badly initialize by initCircuit(LinkedList) method
		} else if (initPath!=this && hasCycle) {
			path  = initPath.path;
			edges = initPath.edges;
			nodes = initPath.nodes;
		}	
		
		return hasCycle;	
	}
	

	
}
