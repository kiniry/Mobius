/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEW;

import umbra.IBytecodeStrings;

/**
 * @author Jaros³aw Paszek
 *
 */
public class NewInstruction extends StringInstruction {

	//&* usuwam grrhh	
	public NewInstruction(String l, String n) {
		super(l, n);
	}
	public boolean correct()
	{
		String s;
		s = extractPoint(line);
		String[] s2 = IBytecodeStrings.anew;
		int j,y;
		for (j = 0; j < s2.length; j++) {
			if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {
				//zakladam ze zawsze z (liczba)
				// w <char lub java.costam> wiec tez nie wiadomo co
				if (s.indexOf("<") < 2) return false;
				if (s.indexOf(">") < 2) return false;
				//&*poprawiam
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
				
				//to dziala dla wszystkich moze by tak isLetter||.
				for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++)
		           {if (!(Character.isDefined(s.charAt(y)))) return false;}
				return true;
			}
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
				//System.out.println("to nie jest cyfra zle ");
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
	
	public Instruction getInstruction() {
	int index;
	//&*
	if (!correct())
		return null;
	index = getInd();

//	   wydaje sie ze dziala dla zmieniania na to samo
//	   aby testowac przy zmianie na inne ciezko sprawdzic
	
	if (name == "anewarray") {
		return new ANEWARRAY(index);
	}
	if (name == "checkcast") {
		return new CHECKCAST(index);
	}
	if (name == "instanceof") {
		return new INSTANCEOF(index);
	}
	if (name == "new") {
		return new NEW(index);
	}
 
	return null;
	
	}

	
}
