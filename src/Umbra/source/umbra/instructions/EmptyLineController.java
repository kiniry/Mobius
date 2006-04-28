/*
 * Created on 2005-05-17
 */
package umbra.instructions;


/**
 * @author Jaros³aw Paszek
 */
public class EmptyLineController extends BytecodeLineController {

	public EmptyLineController(String l) {
		super(l);
	}

	public boolean correct()
	{
		//sprawdzanie poprawnosci juz przy wyborze typu
		return true;
	}

}
