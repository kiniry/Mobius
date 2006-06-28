/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;



/**
 * This is abstract class for all instructions with a string (in or without <>, always without "")
 * as a parameter.
 * 
 * @author Jaros³aw Paszek
 *
 */
public class StringInstruction extends MultiInstruction {

	public StringInstruction(String l, String n) {
		super(l, n);
	}

}
