package annot.formula;

public interface PredicateSymbol {
	public static byte GRT = 0; // ">"
	public static byte GRTEQ = 1; //">="
	public static byte LESS = 2; //"<";
	public static byte LESSEQ = 3; //"<=";
	
	public static byte GRT_uscmp = 4; // ">"
	public static byte GRTEQ_uscmp = 5; //">="
	public static byte LESS_uscmp = 6; //"<";
	public static byte LESSEQ_uscmp = 7; //"<=";
	
	public static byte EQ = 8; //"==";
	
	// this variable must be removed
	public static byte NOTEQ = 9; //"!=";
	public static byte SUBTYPE = 10;//"<:";
	
	
	public static byte INSTANCEOF = 11; // "instanceof";
	public static byte EVEN = 12; // "is even ";
	public static byte ODD = 13; // "is odd";
			
}
