package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownTransitionException;

public enum Transitions {
	equivalent("eguivalent"),
	equals("equals"),
	greaterOrEquals(">="),
	unknown(""),
	prefix("prefix"),
	substring("substring"),
	suffix("suffix");
	
	Transitions(String s){
		reg=s;	
	}
	public String getKind(){
		return reg;
	}
	String reg;
	public static Transitions getTransitionType(String in) {
		for(Transitions id : Transitions.values()){
		  if( id.reg.equals(in)){
		    return id;
		  }
		}
		return unknown;
	}
	
}
