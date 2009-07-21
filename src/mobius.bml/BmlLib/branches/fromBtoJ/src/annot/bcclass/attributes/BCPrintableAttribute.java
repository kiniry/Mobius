package annot.bcclass.attributes;

import annot.bcclass.BCMethod;
import annot.bcclass.BMLConfig;

/**
 * Represents root(?) attributes displayed somewhere
 * in the bytecode (not inside of other displayed attributes)
 * 
 * @author Tomek
 */
public abstract class /*interface?*/ BCPrintableAttribute implements BCAttribute {

	public BCMethod method = null;
	public int pcIndex = -1;
	public String atype = "?";
	
	//will be set by Parsing class, in getAttributeAtLine()
	public int line_start = -1;
	public int line_end = -1;
	
	// abstract
	public String printCode(BMLConfig conf) {
		return "?";
	}
	
	public abstract void replaceWith(BCPrintableAttribute attr);
}
