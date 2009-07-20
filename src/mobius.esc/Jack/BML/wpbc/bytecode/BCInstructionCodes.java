/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface BCInstructionCodes {
	
	
	public static final byte IADD = 0;
	public static final byte LADD = 1;
//	public static final byte FADD = 2;
//	public static final byte DADD = 3;
	
	public static final byte IDIV = 4;
	public static final byte LDIV = 5;
//	public static final byte FDIV = 6;
//	public static final byte DDIV = 7;
	
	public static final byte IMUL = 8;
	public static final byte LMUL = 9;
//	public static final byte FMUL = 10;
//	public static final byte DMUL = 11;
	
	public static final byte  INEG = 12;
	public static final byte  LNEG = 13;
//	public static final byte  FNEG = 14;
//	public static final byte  DNEG = 15;
	
	public static final byte IREM = 14;
	public static final byte LREM = 15;
	
	public static final byte ISUB = 16;
	public static final byte LSUB = 17;
	
	public static final byte ISHL = 18;
	public static final byte LSHL = 19;
	
	public static final byte ISHR = 20;
	public static final byte LSHR = 21;
	
	public static final byte IUSHR = 22;
	public static final byte LUSHR = 23;

	public static final byte IXOR = 24;
	public static final byte LXOR = 25;
	
	public static final byte IOR = 26;
	public static final byte LOR = 27;
	

	public static final byte IAND = 28;
	public static final byte LAND = 29;
	
	public static final byte ATHROW = 30;
	
}
