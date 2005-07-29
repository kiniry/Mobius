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
import java.util.regex.*;

public class Transition extends OrientedEdge implements Comparable, Cloneable{

	public String from;
	public String to;
	public String guard;
	public String update;
	public String synchro; 		//contains a unique method name
	//public boolean synchroEmit; //either '!' or '?' : true if '!'
	public MethodProperty mp;	//remains uninitialized till the instanciation had been processed
	public int synchroType;		//remains uninitialized till the instanciation had been processed
	private boolean succeeded;
	
	
	Transition (Node transition){
		/*|---+transition
			|--- source (ref = Value)
			|--- target (ref = Value)
			|---+label (kind= (synchronisation | update |guard))
				|--- value				
			|---(nail) 
		 */
		//ex: transitionDef = "
		//<transition>
		//   <source ref="id1"/>
		//   <target ref="id0"/>
		//   <label kind="synchronisation" x="8" y="16">closeTransaction_NT?</label>
		//   <nail x="-8" y="88"/><nail x="-8" y="-24"/>
		//</transition>"
		
		from="";
		to="";
		guard="true";
		update="";
		synchro="";		
		succeeded = extractTransition(transition);
	}

	
	/*
	 * 	Modifying functions  
	 * 
	 */

	public int compareTo(Object obj){
		
		int i;
		Transition transition2;
		
		if (! (obj instanceof Transition)) throw new ClassCastException();
		transition2 = (Transition) obj;
		i = this.from.compareTo(transition2.from);
		if (i==0){ i=this.to.compareTo(transition2.to);}
		if (i==0){ i=this.guard.compareTo(transition2.guard);}
		if (i==0){ i=this.update.compareTo(transition2.update);}
		if (i==0){ i=this.synchro.compareTo(transition2.synchro);}
		/*if (i==0){ if ( this.synchroEmit==true && transition2.synchroEmit== false) i=-1;
				   else if (this.synchroEmit==true && transition2.synchroEmit== false) i=1;}*/
		return i;
	}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		//Does it work still after heriting from GraphNode?
		Transition transition = (Transition) super.clone(); 
		transition.from = from;
		transition.to = to;
		transition.guard = guard;
		transition.update = update;
		transition.synchro = synchro; 		
		transition.mp = mp;	
		transition.synchroType = synchroType;
		transition.succeeded = succeeded;
		
		return transition;
	}
	 
	
	
	
	/*
	 * 	Internal modifying functions  
	 * 
	 */
	private boolean extractTransition(Node node){
		Outils o = Outils.outilsFactory();
		Node child;
		String string, value;
		int i,j;
		
		//Verify the nature of the node
		if(o.Name(node).compareToIgnoreCase("transition") != 0) return false; 
		
		for (i=0 ; i < o.childCount(node) ; i++){
			child = o.child(node,i);
			j=0;
			
			if (o.Type(child).compareToIgnoreCase("element")==0 &&
					o.Name(child).compareToIgnoreCase("source") == 0){
				//search transition source name
				while( j < o.attributeCount(child)
						&& o.Name( (o.Attribute(child,j)) ).compareTo("ref") != 0) {j++;}
				if (j >= o.attributeCount(child) ) return false;
				from = o.Value(o.Attribute(child,j));
			}
			else if (o.Type(child).compareToIgnoreCase("element")==0 &&
					o.Name(child).compareToIgnoreCase("target") == 0){
				//search transition target name
				while( j < o.attributeCount(child)
						&& o.Name( (o.Attribute(child,j)) ).compareTo("ref") != 0) {j++;}
				if (j >= o.attributeCount(child) ) return false;
				to = o.Value(o.Attribute(child,j));	
			}
			else if (o.Type(child).compareToIgnoreCase("element")==0 &&
					o.Name(child).compareToIgnoreCase("label") == 0){
				//search label kind
				while( j < o.attributeCount(child)
						&& o.Name( (o.Attribute(child,j)) ).compareTo("kind") != 0) {j++;}
				if (j >= o.attributeCount(child) ) return false;
				string = o.Value(o.Attribute(child,j));	
			
				// verify the nature of the node : should contain a unique text element
				if (o.childCount(child) != 1) return false;
				if (o.Type(o.child(child,0)).compareToIgnoreCase("text")!=0) { return false;}
				value = o.Value(o.child(child,0));
			
				if (string.compareToIgnoreCase("guard")==0 )  {guard = value;}
				else if (string.compareToIgnoreCase("assignment")==0 )  {update = value;}
				else if (string.compareToIgnoreCase("synchronisation")==0 )  {
					synchro = value.substring(0,value.length() -1);
					value = value.substring(value.length() -1);

				}
			}
			/*else {}// ignoring nail //*/
		}
		

		
		
		
		return true;
	}
	
	
	
	/*
	 * 	Access functions  
	 * 
	 */
	
	//TODO remove the getUpdateTestFrom if not used anymore .. 
	public String getUpdateTestForm(){
		String updateTest;   //copy update field
		String[] list;
		Matcher matcher;
		int i;
		
		//System.err.println(update);		
		
		//updateTest = Pattern.compile(",").matcher(updateTest).replaceAll(" && ");
		//updateTest = Pattern.compile(":=").matcher(updateTest).replaceAll("==");
		//Pattern Annotation 	= Pattern.compile("//@.*");
		//Pattern Comment2 = Pattern.compile("(?m)(?i)(?s)/\\*.*?\\*/");
		list = update.split(",");
		
		for (i=0; list.length > i ; i++ ){
			matcher = Pattern.compile("\\s*(.*)\\s*:=\\s*(.*)\\s*").matcher(list[i]);
			if (matcher.find()) {
				updateTest= matcher.group(1);
				updateTest += "==";
				updateTest += "\\old("+matcher.group(2)+")";
				list[i]=updateTest;
			}
		}
		if (i>0){
			updateTest = list[0];
			for (int j=1; j<i ; j++){ updateTest += " && "+list[j]; }
		}
		else updateTest= new String(update);
		
		return updateTest;
	}
	
	
	public String getInterpretedUpdate(){
		String updateTest;   //copy update field
		String[] list;
		Matcher matcher;
		int i,j;
		
		
		//System.err.println("Input  of getInterpretedUpdate is: "+update);
		
		list = update.split(",");
		
		j=0;
		for (i=0; list.length > i ; i++ ){
			//matcher = Pattern.compile("\\s*(.*)\\s*:=\\s*(.*)\\s*").matcher(list[i]);
			matcher = Pattern.compile("(?s)\\s*(.*)\\s*:=\\s*(.*)").matcher(list[i]);
			if (matcher.find()) {
				updateTest= matcher.group(1);
				updateTest += "=";
				updateTest += matcher.group(2);
				list[j] = updateTest;
				j++;
			}
		}
		if (j>0){
			updateTest = list[0];
			for (int k=1; k<j ; k++){ updateTest += " , "+list[k]; } //keep the separation mark : ';' would be a problem in annotations
		}
		else updateTest= new String(update);
		
		
		//System.err.println("Output of getInterpretedUpdate is: "+updateTest);	
		
		return updateTest;

	}
	
	public boolean isGoodTransition() { return succeeded;}
	public String toString() {
		String string;
		string = "TRANSITION : "+super.toString()+"/ ";
		string += "{" + from +"} -> {" + to  + "}";
		if (guard != null)  if (guard.compareTo("")  != 0 ){ string += "\n\tguard  : "+guard ;}
		if (synchro!= null) if (synchro.compareTo("")!= 0 ) {string += "\n\tsynchro: "+synchro ;}
		if (update != null) if (update.compareTo("") != 0 ) { string += "\n\tupdate : "+update ;}
		if (mp instanceof MethodProperty){ 
			string += "\n\tlink transition with method \""+mp.getMethodName()+"\" ";
			string += "(type is "+synchroTypeToString()+")";}
		string += "\n";
		return string;
	}

	public String synchroTypeToString(){ return Outils.outilsFactory().synchroTypeToString(synchroType); }
}
