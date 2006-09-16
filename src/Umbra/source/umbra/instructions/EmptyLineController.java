/*
 * Created on 2005-05-17
 */
package umbra.instructions;


/**
 * 
 * This is a class for a line with whitespaces only.
 * 
 * @author Jarosław Paszek
 */
public class EmptyLineController extends BytecodeLineController {

	/**
	 * TODO
	 */
	public EmptyLineController(String l) {
		super(l);
	}

	/**
	 * @return  true - an empty line is always correct
	 * @see BytecodeLineController#correct()
	 */
	public boolean correct()
	{
		//sprawdzanie poprawnosci juz przy wyborze typu
		return true;
	}

}
