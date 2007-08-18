package annot.formula;

public interface Connector {
	
	public static final byte AND = 1; // "&&";
	public static final byte OR = 2; //"||";
	public static final byte NOT = 3; //"!";
	public static final byte IMPLIES = 4; //"==>";
	public static final byte EQUIV = 5; //"<==>";
	public static final byte NOTEQUIV = 6; //"<=!=>";
}
