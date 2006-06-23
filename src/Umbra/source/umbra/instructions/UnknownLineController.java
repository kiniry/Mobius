/*
 * Created on 2005-05-17
 */
package umbra.instructions;


/**
 * This class is resposible for all lines that we cannot classify.
 * 
 * @author Jaros�aw Paszek
 */
public class UnknownLineController extends BytecodeLineController {

    /**
     * TODO write description
     * 
     * @param l TODO write description 
     */    
    public UnknownLineController(String l) {
		super(l);
	}

	//correct z nadklasy => false
}
