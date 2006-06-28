/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.*;

import umbra.IBytecodeStrings;

/**
 * This class is related to some subset of instructions 
 * depending on parameters. It redefines some crucial while 
 * handling with single instruction methods(correctness, getting handle).
 * Various instructions with no parameter.
 * 
 * @author Jaros³aw Paszek
 */
public class SingleInstruction extends InstructionLineController {
	
	public SingleInstruction(String l, String n) {
		super(l, n);
	}
	
	/**
	 * @see BytecodeLineController#getInstruction()
	 */
	public Instruction getInstruction() {
		//&*
		if (!correct())
			return null;
		if (name == "aconst_null") return new ACONST_NULL();
		if (name == "dadd") return new DADD();
		if (name == "ddiv") return new DDIV();
		if (name == "dmul") return new DMUL();
		if (name == "dneg") return new DNEG();
		if (name == "drem") return new DREM();
		if (name == "dsub") return new DSUB();
		if (name == "fadd") return new FADD();
		if (name == "fdiv") return new FDIV();
		if (name == "fmul") return new FMUL();
		if (name == "fneg") return new FNEG();
		if (name == "frem") return new FREM();
		if (name == "fsub") return new FSUB();
		if (name == "iadd") return new IADD();
		if (name == "iand") return new IAND();
		if (name == "imul") return new IMUL();
		if (name == "idiv") return new IDIV();
		if (name == "ineg") return new INEG();
		if (name == "ior") return new IOR(); 
		if (name == "isub") return new ISUB();
		if (name == "irem") return new IREM();
		if (name == "iushr") return new IUSHR();
		if (name == "ixor") return new IXOR();
		if (name == "lsub") return new LSUB();
		if (name == "ladd") return new LADD();
		if (name == "land") return new LAND();
		if (name == "ldiv") return new LDIV();
		if (name == "lmul") return new LMUL();
		if (name == "lneg") return new LNEG();
		if (name == "lor") return new LOR(); 
		if (name == "lrem") return new LREM();
		if (name == "lshl") return new LSHL();
		if (name == "lshr") return new LSHR();
		if (name == "lushr") return new LUSHR();
		if (name == "lxor") return new LXOR();
		if (name == "aaload") return new AALOAD();
		if (name == "aastore") return new AASTORE();
		if (name == "baload") return new BALOAD();
		if (name == "bastore") return new BASTORE();
		if (name == "caload") return new CALOAD();
		if (name == "castore") return new CASTORE();
		if (name == "daload") return new DALOAD();
		if (name == "dastore") return new DASTORE();
		if (name == "faload") return new FALOAD();
		if (name == "fastore") return new FASTORE();
		if (name == "iaload") return new IALOAD();
		if (name == "iastore") return new IASTORE();
		if (name == "laload") return new LALOAD();
		if (name == "lastore") return new LASTORE();
		if (name == "saload") return new SALOAD();
		if (name == "sastore") return new SASTORE();
		if (name == "arraylength") return new ARRAYLENGTH();
		if (name == "athrow") return new ATHROW();
		if (name == "iconst_0") return new ICONST(0);
		if (name == "iconst_1") return new ICONST(1);
		if (name == "iconst_2") return new ICONST(2);
		if (name == "iconst_3") return new ICONST(3);
		if (name == "iconst_4") return new ICONST(4);
		if (name == "iconst_5") return new ICONST(5);
		if (name == "iconst_m1") return new ICONST(-1);
		if (name == "lcmp") return new LCMP();		
		if (name == "aload_0") return new ALOAD(0);
		if (name == "aload_1") return new ALOAD(1);
		if (name == "aload_2") return new ALOAD(2);
		if (name == "aload_3") return new ALOAD(3);
		if (name == "astore_0") return new ASTORE(0);
		if (name == "astore_1") return new ASTORE(1);
		if (name == "astore_2") return new ASTORE(2);
		if (name == "astore_3") return new ASTORE(3);
		if (name == "dload_0") return new DLOAD(0);
		if (name == "dload_1") return new DLOAD(1);
		if (name == "dload_2") return new DLOAD(2);
		if (name == "dload_3") return new DLOAD(3);
		if (name == "dstore_0") return new DSTORE(0);
		if (name == "dstore_1") return new DSTORE(1);
		if (name == "dstore_2") return new DSTORE(2);
		if (name == "dstore_3") return new DSTORE(3);
		if (name == "fload_0") return new FLOAD(0);
		if (name == "fload_1") return new FLOAD(1);
		if (name == "fload_2") return new FLOAD(2);
		if (name == "fload_3") return new FLOAD(3);
		if (name == "fstore_0") return new FSTORE(0);
		if (name == "fstore_1") return new FSTORE(1);
		if (name == "fstore_2") return new FSTORE(2);
		if (name == "fstore_3") return new FSTORE(3);
		if (name == "iload_0") return new ILOAD(0);
		if (name == "iload_1") return new ILOAD(1);
		if (name == "iload_2") return new ILOAD(2);
		if (name == "iload_3") return new ILOAD(3);
		if (name == "istore_0") return new ISTORE(0);
		if (name == "istore_1") return new ISTORE(1);
		if (name == "istore_2") return new ISTORE(2);
		if (name == "istore_3") return new ISTORE(3);
		if (name == "lload_0") return new LLOAD(0);
		if (name == "lload_1") return new LLOAD(1);
		if (name == "lload_2") return new LLOAD(2);
		if (name == "lload_3") return new LLOAD(3);
		if (name == "lstore_0") return new LSTORE(0);
		if (name == "lstore_1") return new LSTORE(1);
		if (name == "lstore_2") return new LSTORE(2);
		if (name == "lstore_3") return new LSTORE(3);
		if (name == "monitorenter") return new MONITORENTER();
		if (name == "monitorexit") return new MONITOREXIT();
		if (name == "areturn") return new ARETURN();
		if (name == "dreturn") return new DRETURN();
		if (name == "freturn") return new FRETURN();
		if (name == "ireturn") return new IRETURN();
		if (name == "lreturn") return new LRETURN();
		if (name == "return") return new RETURN();
		if (name == "dup") return new DUP();
		if (name == "dup_x1") return new DUP_X1();
		if (name == "dup_x2") return new DUP_X2();
		if (name == "dup2") return new DUP2();
		if (name == "dup2_x1") return new DUP2_X1();
		if (name == "dup2_x2") return new DUP2_X2();
		if (name == "pop") return new POP();
		if (name == "pop2") return new POP2();
		if (name == "swap") return new SWAP();
		return null;
	}

	/**
	 * Simple instruction line is correct if it has 
	 * no parameter
	 * 
	 *@see InstructionLineController#correct() 
	 */
	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.single;
		int j;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) 
				if (((s.indexOf(s2[j])) + (s2[j].length())) == s.length())
				    return true;
		}
		return false;
	}
}
