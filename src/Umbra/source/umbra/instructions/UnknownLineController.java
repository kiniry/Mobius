/*
 * Created on 2005-05-17
 */
package umbra.instructions;


/**
 * This class is resposible for all lines that we cannot classify.
 * 
 * @author Jarosław Paszek
 */
public class UnknownLineController extends BytecodeLineController {

	/**
	 * This constructor only remembers the line with the
	 * unrecognized content
	 * 
	 * @param l the line with the unrecognized content
	 */
	public UnknownLineController(String l) {
		super(l);
	}

}
