/*
 * Created on 2005-05-18
 *
 */
package umbra.instructions;


/**
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
	
	public void setIndex(int index2) {
		this.index = index2 + 1;
	}

}
