package annot.bcclass;

import org.apache.bcel.classfile.Method;

/**
 * This class represents display style and environment for
 * BML attributes. 
 * 
 * @author Tomekb
 *
 */
public class BMLConfig {
	// constant pool
	private	BCConstantPool cp;
	
	// method that is currently being displayed
	public Method currMethod;
	
	// true iff expressions should be displayed
	// in debug (raw) mode
	public boolean goControlPrint = false;
	
	// priority of the parent of the currently
	// displayed expression
	public int root_pri;
	
	// used in controlPrint as a prefix of each
	// line of expression (sequence of spaces)
	public String wciecie;
	
	// position in current line (for expression.printCode*(),
	// line breaking)
	public int line_pos;
	
	// depth of currrently displayed expression
	// in expression tree
	public int expr_depth;
	
	public BMLConfig(BCConstantPool cp) {
		this.cp = cp;
	}
	
	public BCConstantPool getConstantPool() {
		return cp;
	}
}
