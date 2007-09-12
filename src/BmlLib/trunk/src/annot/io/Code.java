package annot.io;

public interface Code {
	public static final int TRUE = 0x00;
	public static final int FALSE = 0x01;
	public static final int AND = 0x02;
	public static final int OR = 0x03;
	public static final int IMPLIES = 0x04;
	public static final int NOT = 0x05;
	public static final int FORALL = 0x06;
	public static final int EXISTS = 0x07;

	public static final int EQ = 0x10;
	public static final int GRT = 0x11;
	public static final int LESS = 0x12;
	public static final int LESSEQ = 0x13;
	public static final int GRTEQ = 0x14;
	public static final int NOTEQ = 0x17;

	public static final int INT_LITERAL = 0x40;
	public static final int JAVA_TYPE = 0xC0;
	public static final int BOUND_VAR = 0xE0;

	// XXX check opcodes
	public static final int FORALL_WITH_NAME = 0xE1;
	public static final int EXISTS_WITH_NAME = 0xE2;

	// codes NOT included in .class file format (but used as connectors):
	public static final int EQUIV = 0x08;
	public static final int NOTEQUIV = 0x09;

	public static final int CONSTANT_UTF8 = 1;

}
