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

	public String toString() {
		if (path == null) {
			return "empty";
		} 
		Enumeration en = path.elements();
		Integer instrPos;
		
		String  s = ""; 
		while (en.hasMoreElements()) {
			instrPos = (Integer) en.nextElement();
			s = s  + " " +instrPos.intValue();
		}
		return s ;
	}

	/**
	 * 
	 * @param instr
	 * @return false if the path doesnot contain a block that contains this
	 *         instruction true otherwise
	 */
	public boolean contains(BCInstruction _instr) {
		Enumeration en = path.elements();
		BCInstruction instr;
		while (en.hasMoreElements()) {
			Integer instrPos = (Integer) en.nextElement();
			if (_instr.getPosition() == instrPos.intValue()) {
				return true;
			}
		}
		return false;
	}

	/*public void addInstrToPath(BCInstruction instr) {
		if (path == null) {
			path = new Vector();
		}
		path.add(new Integer(instr.getPosition()));
	}*/
	
	public void addInstrToPath(Integer instrPos) {
		if (path == null) {
			path = new Vector();
		}
		path.add(instrPos);
	}

	public Path copy() {
		Path copyPath = new Path();
		Vector copyVector = new Vector();
		Enumeration en = path.elements();
		/*
		 * while (en.hasMoreElements()) { BCInstruction instr = (BCInstruction)
		 * en.nextElement(); copyPath.addInstrToPath( instr ); }
		 */
		while (en.hasMoreElements()) {
			Integer instrPos = (Integer) en.nextElement();
			copyPath.addInstrToPath(instrPos);
		}
		return copyPath;
	}

	

	
}