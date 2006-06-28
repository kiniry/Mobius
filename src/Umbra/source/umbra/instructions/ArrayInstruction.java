/*
 * Created on 2005-05-19
 */
package umbra.instructions;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.Type;

import umbra.IBytecodeStrings;

/**
 * This class is related to some subset of instructions 
 * depending on parameters. It redefines some crucial while 
 * handling with single instruction methods(correctness, getting handle).
 * There is only one array instruction used to create new
 * array of a particular type.
 * 
 * @author Jaros³aw Paszek
 */
public class ArrayInstruction extends StringInstruction {

	private final String names[] =
	{"VOID", "BOOLEAN","INT", "SHORT", "BYTE", "LONG",
		"DOUBLE", "FLOAT", "CHAR"};

	private final Type types[] =
	{Type.VOID, Type.BOOLEAN, Type.INT, Type.SHORT,
			Type.BYTE, Type.LONG, Type.DOUBLE,
			Type.FLOAT, Type.CHAR};
	
	private final int typeCount = types.length;

	private Type getType(String insName) {
		for (int i = 0; i < typeCount; i++) {
			if ((names[i].startsWith(insName)) && (insName.startsWith(names[i])))
				return types[i];
		};
		return null;
	}
		
	public ArrayInstruction(String l, String n) {
		super(l, n);
	}

	/**
	 * @see BytecodeLineController#getInstruction()
	 */
	
	public Instruction getInstruction() {
		//System.out.println("ArrayInstruction->getInstruction...");
		String insType = line.substring(line.indexOf("<") + 1, line.indexOf(">"));
		insType = insType.toUpperCase();
		if (getType(insType) == null) {
			//System.out.println("   Wrong instruction argument!");
			return null;
		}
		byte r = getType(insType).getType();
		//&*
		boolean isOK = correct();
		if (isOK) {
		if (name == "newarray")
			return new NEWARRAY(r);
		}
		//System.out.println("   Failed!");
		return null;
	}

	
	/**
	 * Array instruction line is correct if it has 
	 * one parameter that is class (or non-classed type) name.
	 * 
	 *@see InstructionLineController#correct() 
	 */

	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.array;
		int j,y;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {
				//System.out.println(s);
				//System.out.println("array " + s);
				if (s.indexOf("<") < 2) return false;
				if (s.indexOf(">") < 2) return false;
				// zmienione 7.26.15
				String insType = s.substring(s.indexOf("<") + 1, s.indexOf(">"));
				insType = insType.toUpperCase();
				if (getType(insType) == null) {
					System.out.println("E04");
					return false;
				}
				
				for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++)
		           {if (!(Character.isDefined(s.charAt(y)))) return false;}
				return true;
			}
		}
			
		return false;
	}
}
