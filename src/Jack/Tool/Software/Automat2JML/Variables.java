/*
 * Created on Mar 16, 2005
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




public class Variables implements Comparable, Cloneable{

	public String type;
	public String name;
	public String initValue;
	public String annotation; 
	
	Variables(){
			type = "";
			name = "";
			initValue= "";
			annotation="";
	}
	
	
	public String getInterpretedType(){
		
		if (type.compareTo("bool")==0) return "boolean";
		
		
		
		return type;
	
	}
	
	
	//
	public String toString(){
		
		String string = ""; 
		if (annotation != null) {string += annotation+" \n";}
		string += "type="+type+" ;name="+name+" ;" ;
		if (initValue  != null) {string += "initValue="+initValue +" ;";}

		return string ;
	}
	
	//implementing interface
	public int compareTo(Object obj){
	
		int i;
		Variables var2;
		
		if(!(obj instanceof Variables)) throw new ClassCastException();
		var2=(Variables)obj;
		i = this.name.compareTo(var2.name);
		if (i==0) {i = this.type.compareTo(var2.type);};
				
		return i;
	}
 	protected Object clone()  throws CloneNotSupportedException
	{ 
		return super.clone();
	}
	
}
