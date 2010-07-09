package ie.ucd.semantic_properties_plugin.file_checker;

public enum Transitions {
	equivalent("eguivalent"),equals("equals"),greaterOrEgual(">="),unknown("");
	Transitions(String s){
		reg=s;	
	}
	public String getKind(){
		return reg;
	}
	String reg;
	public static Transitions getTransitionType(String in){
		if(in.equals("equivalent"))
			return Transitions.equivalent;
		else if(in.equals("equals"))
			return Transitions.equals;
		else
			return Transitions.unknown;
		
	}
}
