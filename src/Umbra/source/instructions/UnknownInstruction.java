/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;


/**
 * @author Tomek Batkiewicz i Jaros³aw Paszek
 *
 */
public class UnknownInstruction extends InstructionLineController {

	//&* usuwam grrhh
	
	public UnknownInstruction(String l, String n) {
		super(l, n);
	}
	public boolean correct()
	{
		return false;
	}
}
