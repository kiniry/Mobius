/*
 * Created on Jun 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode.block;

import java.util.Enumeration;
import java.util.Vector;

import utils.Util;

import formula.Formula;

import bcclass.attributes.ExsuresTable;
import bytecode.BCInstruction;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Path {
	public Vector path;

	public Path() {
	}

	public void dump() {
		Enumeration en = path.elements();
		BCInstruction instr;
		while (en.hasMoreElements()) {
			instr = (BCInstruction) en.nextElement();
			Util.dump(instr.toString());
		}
	}
	/**
	 * 
	 * @param instr
	 * @return false if the path doesnot contain a block that contains this instruction
	 * 				true otherwise
	 */
	public boolean contains(BCInstruction _instr) {
		Enumeration en = path.elements();
		BCInstruction instr;
		while (en.hasMoreElements()) {
			instr  = (BCInstruction)en.nextElement();
			if (_instr == instr) {
				return true;
			}
		}
		return false;
	}

	public void addBlockToPath(BCInstruction instr) {
		if (path == null) {
			path = new Vector();
		}
		path.add(instr);
	}
	
	public Path copy() {
		Path copyPath = new Path();
		Vector copyVector = new Vector();
		Enumeration en =  path.elements();
		while (en.hasMoreElements()) {
			BCInstruction instr = (BCInstruction) en.nextElement();
			copyPath.addBlockToPath( instr );
		}
		return copyPath;		
	}
	
//	/**
//	 * calculates the wp for this path and returns the result
//	 * @param _normal_post
//	 * @param exsTable
//	 * @return
//	 */
//	public Formula wp(Formula _normal_post, ExsuresTable _exc_Postcondition) {
//		Formula wp = _normal_post.copy() ;
//		for (int i = blocks.size() - 1 ; i >= 0; i--) {
//			Block b = (Block)blocks.elementAt(i);
//			wp  = b.wp( wp, _exc_Postcondition );
//		}	 
//		return wp;
//	}
}
