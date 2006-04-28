/*
 * Created on 2005-05-18
 *
 */
package umbra.instructions;


/**
 * @author Tomek Batkiewicz i Jaros³aw Paszek
 *
 */
public class ThrowsLineController extends BytecodeLineController {
	
	public ThrowsLineController(String l) {
		super(l);
	}

	public boolean correct()
	{
		//tez niezbyt - patrz przy wyborze typu - nie za bardzo wiemy jak wyglada
		return true;
	}
}
