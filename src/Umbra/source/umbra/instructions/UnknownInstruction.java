/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;


/**
 * This is a class resposible for all lines which are regarded
 * to be an instruction but unable to classify.
 * 
 * @author Tomek Batkiewicz i Jaros³aw Paszek
 */
public class UnknownInstruction extends InstructionLineController {
	
	
	public UnknownInstruction(String l, String n) {
		super(l, n);
	}
/**
 * Instruction out of classification must be obviously incorrect.
 * @see		InstructionLineController#correct()
 */
	public boolean correct()
	{
		return false;
	}
}
