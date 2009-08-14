/*
 * Created on 2005-12-18
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package canapa.util;

import antlr.CommonHiddenStreamToken;
import jparse.FileAST;
import jparse.JavaAST;
import jparse.TypeAST;

/**
 * @author DzinX
 */
public class TreeWalker {
	private FileAST tree;
	private JavaAST current, previous;
	public TreeWalker(FileAST tree) {
		this.tree = tree;
		current = previous = null;
	}
	
	public void insertJMLbefore(String annotation) {
		CommonHiddenStreamToken x = current.addHiddenBefore(annotation);
		previous.setHiddenAfter(x);
	}
	
	private boolean ge(CommonHiddenStreamToken token, Location loc) {
		return ((loc.getLine() < token.getLine()) || ((loc.getLine() == token.getLine())
				&& (loc.getColumn() <= token.getColumn())));
	}
	
	private boolean astTypeOK() {
		String txt = current.getText();
		String classname = current.getClass().getName();
		if (classname.indexOf("JavaAST") >= 0)
			if (txt != null) {
				if (current.getText().equals("PARAMETERS"))
				return false;
			}
		if (classname.indexOf("ModifierAST") >= 0)
			return false;
		if (classname.indexOf("TypeAST") >= 0)
			return false;
		if (classname.indexOf("ParameterAST") >= 0)
			return false;
		return true;
	}
	
	private boolean findParamNode(Location loc) {
		if (current == null)
			return false;
		CommonHiddenStreamToken before = current.getHiddenBefore();
		CommonHiddenStreamToken after = current.getHiddenAfter();
		if (after == null) {
				//idziemy dalej
			} else {
				//before null
				//after not null
				if (ge(after, loc)) {
					if (astTypeOK())
						return true;
				}
			}
		JavaAST oldCurrent = current;
		if (astTypeOK())
			previous = current;
		current = current.getSon();
		boolean result = findParamNode(loc);
		if (result)
			return true;
		//previous = oldCurrent; //maybe not
		current = oldCurrent.getBrother();
		return findParamNode(loc);
	}
	
	public boolean setAtParamNode(Location loc) {
		current = tree;
		previous = null;
		boolean success = findParamNode(loc);
		return success;
	}
}
