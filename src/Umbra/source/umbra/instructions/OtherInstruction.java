/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;


/**
 * This is abstract class for all instructions which are 
 * correct with number parameter as well as with a string 
 * one (in "").
 * 
 * @author Jaros³aw Paszek
 *
 */
public class OtherInstruction extends MultiInstruction {

	public OtherInstruction(String l, String n) {
		super(l, n);
	}

}
