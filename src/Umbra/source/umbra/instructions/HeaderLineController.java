/*
 * Created on 2005-05-18
 *
 */
package umbra.instructions;


/**
 * This is a class for a special Bytecode lines at the beginning
 * of the method, not to be edited by a user.
 * 
 * @author Tomek Batkiewicz
 */
public class HeaderLineController extends BytecodeLineController {

	public HeaderLineController(String l) {
		super(l);
	}
	
	public boolean correct()
	{
		//niz za bardzo mozna ustalic zaleznosci
		//zbior wyrazow przed innym niektore opcjonalne
		return true;
	}
	
	/**
	 * The method index of the header is equal to
	 * the previous line's one increased by one.
	 */
	
	public void setIndex(int index2) {
		this.index = index2 + 1;
	}

}
