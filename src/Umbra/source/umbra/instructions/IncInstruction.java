/*
 * Created on 2005-05-19
 */
package umbra.instructions;

import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.Instruction;

import umbra.IBytecodeStrings;

/**
 * This class is related to some subset of instructions 
 * depending on parameters. It redefines some crucial while 
 * handling with single instruction methods(correctness, getting handle).
 * This is only dealing with iinc instruction.
 * 
 * @author Jaros³aw Paszek i Tomasz Batkiewicz 
 */
public class IncInstruction extends NumInstruction {

	
	
	public IncInstruction(String l, String n) {
		super(l, n);
	}

	
	/**
	 * Inc instruction line is correct if it has 
	 * two simple number parameters (first preceded with %).
	 * 
	 *@see InstructionLineController#correct()
	 *@see InstructionLineController#chkcorr(String, String) 
	 */
	public boolean correct() {
		return super.chkcorr(line, "W%DW?-D?W");
	}
	
	public boolean correct0()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.incc;
		int j;
		int y;
		int okok;
		System.out.print(s);
		if (s.indexOf("%") < s.indexOf(":") + 1) {
			System.out.print("hej1");
			return false;
		}
		boolean isminus = false;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) 
				if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%"))
				{   
					for (y = (s.indexOf("%") + 1); y < s.length(); y++)
						{
						if (!(Character.isDigit(s.charAt(y)))) {
							System.out.print("tu ten minus " + s + " " + line);
							if (isminus) {return false;}
							else if (s.charAt(y)== '-' ) {isminus = true;}
							else {return false;}
						}
						}
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
				  if (counter == 2) return true;
				}
				  	
		}
		return false;
	}

	private int getInd1() {
		boolean isd;
		String licznik = "0123456789";
		int liczba = 0;
		
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
	
	private int getInd2() {
		boolean isd;
		String licznik = "0123456789";
		int liczba = 0;
		
		isd = true;	
		//sets after first number parameter
		int skadskad = line.length();
		for (int i = line.lastIndexOf("%") + 1;i < line.length();i++) {
			if (!Character.isDigit(line.charAt(i))){
				skadskad = i;
				break;
			}
		}
		//sets the starting point of second number parameter
		int skad = 0;
		for (int i = skadskad;i < line.length();i++) {
			if (Character.isDigit(line.charAt(i))){
				skad = i;
				break;
			}
		}
		//sets the ending point of second number parameter		
		int dokad = line.length();
		for (int i = skad;i < line.length();i++) {
			if (!Character.isDigit(line.charAt(i))){
				dokad = i;
				break;
			}
		}
		
		
		//always convert to int 
		if (isd){
			liczba = 0;
			for (int i = skad;i < dokad;i++) {
				liczba = 10*liczba + licznik.indexOf(line.substring(i,i+1));
			}
			if (line.charAt(skad - 1) == '-') {
				liczba = liczba*(-1);
			}
			return liczba;
		}
		return 0;
	}
	
	/**
	 * @see BytecodeLineController#getInstruction()
	 */
	
	public Instruction getInstruction() {
		
		if (!correct())
			return null;
		
		int index1 = 0;
		index1 = getInd1();
		int index2 = 0;
		index2 = getInd2();
		
		if (name == "iinc") {
			return new IINC(index1, index2);
		}
		
		return null;
		
		}
	
	
}
