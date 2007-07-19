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
	// constant pool; XXX unused?
	private	BCConstantPool cp;
	
	// method that is currently being displayed
	public Method currMethod;
	
	// true iff expressions should be displayed
	// in debug (raw) mode
	public boolean goControlPrint = false;
	
	// using old, smartless line breaking algorithm
	public boolean goSimpleLineBreaking = false;
	
	// priority of the parent of the currently
	// displayed expression
	public int root_pri;
	
	// used in controlPrint as a prefix of each
	// line of expression (sequence of spaces)
	public String wciecie;
	
	// position in current line (for expression.printCode*(),
	// line breaking)
	public int line_pos;
	
	public final int max_total_line_width = 40;
	
	// maximum annotation line width
	public int max_line_width = max_total_line_width - 4;
	
	// depth of currrently displayed expression
	// in expression tree
	public int expr_depth;
	
	// TODO: unused (!)
	// this two characters in expressions are reserved
	// for line-breaking procedure and shouldn't appear
	// anywhere else in expressions
	public char expr_block_start = '{';
	public char expr_block_end = '}';
	
	public BMLConfig(BCConstantPool cp) {
		this.cp = cp;
	}
	
	// beginning of the annotation's line
	public String newLine() {
		max_line_width = max_total_line_width - wciecie.length() + 1;
		return "\n *  " + wciecie;
	}
	
	// surrounds annotation str with comment brackets
	// XXX unused?
	public String addComment(String str) {
		if (str.lastIndexOf("\n") >= 0) {
			return "/*  " + str + "\n */\n";
		} else {
			return "/*  " + str + "  */\n";
		}
	}
}
