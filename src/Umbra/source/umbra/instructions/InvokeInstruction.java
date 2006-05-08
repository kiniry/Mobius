/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;

import umbra.IBytecodeStrings;

/**
 * This class is related to some subset of instructions 
 * depending on parameters. It redefines some crucial while 
 * handling with single instruction methods(correctness, getting handle).
 * Instructions of this kind are used to call other methods.
 * 
 * @author Jaros³aw Paszek
 */
public class InvokeInstruction extends StringInstruction {

	
	public InvokeInstruction(String l, String n) {
		super(l, n);
	}
	
	
	/**
	 * Invoke instruction line is correct if its parameter 
	 * contains class name at the beginning and a number in ()
	 * at the end.
	 * 
	 *@see InstructionLineController#correct() 
	 */

	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.invoke;
		int j;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) 
				
				if (s.lastIndexOf("(") < 2) return false;
				if (s.lastIndexOf(")") < 2) return false;
				int m,n,o;
				m = line.lastIndexOf("(");
				n = line.lastIndexOf(")");
				if (m + 1 >= n) {return false;}
				for (o = m + 1; o < n; o++) 
					{ if (!(Character.isDigit(line.charAt(o))))
						{return false;}
					}
				return true;
		}
		return false;
	}
	
	private int getInd() {
		boolean isd;
		String licznik = "0123456789";
		int liczba;
		if (line.lastIndexOf("(") >= line.lastIndexOf(")")){
		} else {
		isd = true;	
		for (int i = line.lastIndexOf("(") + 1;i < line.lastIndexOf(")");i++) {
			if (!Character.isDigit(line.charAt(i))){
				isd = false;
			}
		}
		if (isd){
			liczba = 0;
			for (int i = line.lastIndexOf("(") + 1;i < line.lastIndexOf(")");i++) {
				liczba = 10*liczba + licznik.indexOf(line.substring(i,i+1));
			}
			return liczba;
		}
		}
		return 0;
	}
	
	/**
	 * @see BytecodeLineController#getInstruction()
	 */
	
	public Instruction getInstruction() {
	int index;
	index = getInd();
	
	if (!correct())
		return null;
	
	if (name == "invokespecial") {
		return new INVOKESPECIAL(index);
	}
	if (name == "invokestatic") {
		return new INVOKESTATIC(index);
	}
	if (name == "invokevirtual") {
		return new INVOKEVIRTUAL(index);
	}
 
	return null;
	
	}
	
	
}
