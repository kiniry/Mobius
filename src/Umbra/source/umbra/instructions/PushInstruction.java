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
 * Here are two instructions resposible for pushing onto the stack.
 * 
 * @author Jaros³aw Paszek
 *
 */
public class PushInstruction extends NumInstruction {
	
	public PushInstruction(String l, String n) {
		super(l, n);
	}
	
	/**
	 * Push instruction line is correct if it has 
	 * one simple number parameter.
	 * 
	 *@see InstructionLineController#correct() 
	 */
	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.push;
		int j;
		int y;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) 
				{ for (y = ((s.indexOf(s2[j])) + (s2[j].length())); y < s.length(); y++)
						{if (!(Character.isDigit(s.charAt(y)))) return false;}
			      int a,b;
			      int counter = 0;
			      boolean lastisdig = false;
				  for (y = ((line.indexOf(s2[j])) + (s2[j].length()) + 1);y < line.length(); y++){
			      	if (Character.isDigit(line.charAt(y))) {
			      		if (!(lastisdig)) {counter++;}
			      		lastisdig = true;
			      	} else 
			      		if (Character.isWhitespace(line.charAt(y))) {
			      			lastisdig = false;}
			      }
				  if (counter == 1) return true;
				}	
		}
		return false;
	}
	
	private int getInd() {
		boolean isd;
		String licznik = "0123456789";
		int liczba;
		
		String line1;
		line1 = extractPoint(line);
		
		isd = true;	
		// zakladam ze poprawnosc jest juz wyzej
		int dokad = line1.length();
		int skad = line1.indexOf(name) + name.length();
		
		if (isd){
			liczba = 0;
			for (int i = skad;i < dokad;i++) {
				liczba = 10*liczba + licznik.indexOf(line1.substring(i,i+1));
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
		if (!correct())
			return null;
		index = getInd();
		
		byte b = 0;
		b = (byte)index;
		
		if (name == "bipush") {
			return new BIPUSH(b);
		}
		if (name == "sipush") {
			return new SIPUSH(b);
		}
		

		return null;
		
		}
	
}
