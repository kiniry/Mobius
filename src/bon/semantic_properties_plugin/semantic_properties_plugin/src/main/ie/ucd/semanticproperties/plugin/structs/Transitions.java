package ie.ucd.semanticproperties.plugin.structs;

public enum Transitions {
	equivalent("eguivalent"),
	equals("equals"),
	greaterOrEgual(">="),
	unknown(""),
	prefix("prefix"),
	substring("substring"),
	suffix("sufix");
	
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
		else if(in.equals("prefix"))
			return Transitions.prefix;
		else if(in.equals("equals"))
			return Transitions.equals;
		else
			return Transitions.unknown;
		
	}
}
