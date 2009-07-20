/*
 * Created on Mar 11, 2005
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


//Definition of the node type
import org.w3c.dom.Node;

public class State extends GraphNode implements Comparable, Cloneable{
	
	public String name;
	public String reference;
	public String invariant;
	public String type; // {init, urgent, commit} U {standard}
	private boolean succeeded;

	State(Node state) {
		/*	+location (id=value)
		 	|---+name
		 		|--- value
		    |---+label (kind= invariant)
				|--- value
			|--- init 
			|--- commit
			|--- urgent  */
		//ex: state =   
		//  <location id="id0" x="-32" y="-48">
		//		<name x="-24" y="-104">ZeroTransaction</name>
		//		<label kind="invariant" x="0" y="-64">x&lt;5 and y&lt;2</label>
		//		</commit> ou </urgent>
		//	</location>
		type = "standard";
		name="";
		reference="";
		invariant="";
		succeeded = extractState(state);
		
	}
	
	/*
	 * 	Modifying functions  
	 * 
	 */
	public void setInit(){type = "init";}
	
	
	
	public int compareTo(Object obj){
		
		int i;
		State state2;
		
		if(!(obj instanceof State)) throw new ClassCastException();
		state2=(State)obj;
		i = this.name.compareTo(state2.name);
		if (i==0) {i = this.reference.compareTo(state2.reference);}
		if (i==0) {i = this.type.compareTo(state2.type);}
		if (i==0) {i = this.invariant.compareTo(state2.invariant);}

		return i;
	}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		//Does it work still after heriting from GraphNode?
		
		State state = (State) super.clone(); 
		state.name = name;
		state.reference = reference;
		state.invariant = invariant;
		state.type =  type; 
		state.succeeded = succeeded;
		return state;
	}
		
	/*
	 * 	Internal modifying functions  
	 * 
	 */
	private boolean extractState(Node node){
		Outils o = Outils.outilsFactory();
		Node child;
		int j=0;
		
		//Verify the nature of the node
		if(o.Name(node).compareToIgnoreCase("location") != 0) return false; 
		//search the state reference number in the attributes of the node
		while( j < o.attributeCount(node)
				&& o.Name( (o.Attribute(node,j)) ).compareTo("id") != 0) {j++;}
		if (j >= o.attributeCount(node) ) return false;
		
		reference = o.Value( o.Attribute(node,j) ); 
		name = reference;
		
		//extract labels and name
		for (j=0 ; j < o.childCount(node) ; j++){
			
			child = o.child(node, j);
			
			//if it is a label
			if (o.Name(child).compareToIgnoreCase("label") ==0 &&
					o.Type(child).compareToIgnoreCase("element")==0){
				//Attribute must declare an invariant
				if (o.childCount(child) != 1 ) return false;
				if (o.Type(o.child(child, 0)).compareToIgnoreCase("text")==0 ) 
					invariant = o.Value( o.child(child, 0) );
			}
			//else if it is a name
			else if (o.Name(child).compareToIgnoreCase("name")==0 &&
					o.Type(child).compareToIgnoreCase("element")==0){
				if (o.childCount(child) != 1 ) return false;
				if (o.Type(o.child(child, 0)).compareToIgnoreCase("text")==0 ) 
					name = o.Value( o.child(child, 0) );				
			}
			else if (o.Name(child).compareToIgnoreCase("init")==0 &&
					o.Type(child).compareToIgnoreCase("element")==0){
				
			}
			else if (o.Name(child).compareToIgnoreCase("urgent")==0 &&
					o.Type(child).compareToIgnoreCase("element")==0){
				type = "urgent";
			}
			else if (o.Name(child).compareToIgnoreCase("commit")==0 &&
					o.Type(child).compareToIgnoreCase("element")==0){
				type = "commit";
			}
		}
		
		return true;
	}
	
	
	/*
	 * 	Access functions  
	 * 
	 */
	public boolean isGoodState() { return succeeded;}
	public boolean isInitial(){ return (type.compareToIgnoreCase("init")==0);}
	public boolean isUrgent(){ return (type.compareToIgnoreCase("urgent")==0);}
	public boolean isCommit(){ return (type.compareToIgnoreCase("commit")==0);}
	public String toString() {
		String string;
		string = "STATE: "+super.toString()+"/"+name+"\n";
		if (invariant.compareTo("")!= 0 ) { string += "\tinvariant: "+invariant;}
		if (type.compareTo("")     != 0 ) { string += "\ttype: "+type  ;}
		
		return string;
	}
	
}
