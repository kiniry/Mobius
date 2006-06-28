/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.ALOAD;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.DLOAD;
import org.apache.bcel.generic.DSTORE;
import org.apache.bcel.generic.FLOAD;
import org.apache.bcel.generic.FSTORE;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LLOAD;
import org.apache.bcel.generic.LSTORE;

import umbra.IBytecodeStrings;

/**
 * This class is related to some subset of instructions 
 * depending on parameters. It redefines some crucial while 
 * handling with single instruction methods(correctness, getting handle).
 * Load and store instrucions.
 * 
 * @author Jaros³aw Paszek
 *
 */
public class StackInstruction extends NumInstruction {

	public StackInstruction(String l, String n) {
		super(l, n);
	}
	
	/**
	 * Stack instruction line is correct if it has 
	 * one number parameter preceded with %.
	 * 
	 *@see InstructionLineController#correct() 
	 */
	
	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.stack;
		int j;
		int y;
		if (s.indexOf("%") < s.indexOf(":") + 1) 
			return false;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) 
				if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%"))
				{ for (y = (s.indexOf("%") + 1); y < s.length(); y++)
						{if (!(Character.isDigit(s.charAt(y)))) 
						    return false;}
				int a,b,d,e,f,g;  
				a = (s.length() - s.indexOf("%"));
				int c = 0;
				e = line.length() - line.indexOf("%");
				f = 0; g = line.length();
				for (d = 0; d < e; d++)
				  { if (Character.isDigit(line.charAt(g - d - 1)))
				       {f = 1;}
					if (f == 0) {
				      if (Character.isWhitespace(line.charAt(g - d - 1)))
				       {c++;}
					}
				  }
					
				b = e - c;
				if (a == b)
					return true;
				}	
		}
		return false;
	}
	
	
	private int getInd() {
		boolean isd;
		String licznik = "0123456789";
		int liczba;
		
		isd = true;	
		int dokad = line.length();
		for (int i = line.lastIndexOf("%") + 1;i < line.length();i++) {
			if (!Character.isDigit(line.charAt(i))){
				dokad = i;
				break;
			}
		}
		if (isd){
			liczba = 0;
			for (int i = line.lastIndexOf("%") + 1;i < dokad;i++) {
				liczba = 10*liczba + licznik.indexOf(line.substring(i,i+1));
			}
			return liczba;
		}
		return 0;
	}
	/**
	 * @see BytecodeLineController#getInstruction()
	 */
	
	public Instruction getInstruction() {
		int index = 0;
		//&*
		if (!correct())
			return null;
		index = getInd();
		
		if (name == "aload") {
			return new ALOAD(index);
		}
		if (name == "astore") {
			return new ASTORE(index);
		}
		if (name == "dload") {
			return new DLOAD(index);
		}
		if (name == "dstore") {
			return new DSTORE(index);
		}
		if (name == "fload") {
			return new FLOAD(index);
		}
		if (name == "fstore") {
			return new FSTORE(index);
		}
		if (name == "iload") {
			return new ILOAD(index);
		}
		if (name == "istore") {
			return new ISTORE(index);
		}
		if (name == "lload") {
			return new LLOAD(index);
		}
		if (name == "lstore") {
			return new LSTORE(index);
		}

		
		return null;
		
		}
	
}
