/*
 * Created on Jun 7, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package org.gjt.jclasslib.structures.jmlattributes;

import java.io.DataInput;
import java.io.IOException;

/**
 *
 *  @author L. Burdy
 **/
public class MethodSpec {

	Formula requires;
	Formula[] modifies;
	Formula ensures;
	Exsures[] exsures;

	MethodSpec(DataInput in) throws IOException {
		requires = new Formula(in);
		modifies = new Formula[in.readUnsignedShort()];
		for (int i = 0; i < modifies.length; i++)
			modifies[i] = new Formula(in);
		ensures = new Formula(in);
		exsures = new Exsures[in.readUnsignedShort()];
		for (int i = 0; i < exsures.length; i++)
			exsures[i] = new Exsures(in);
	}

	public String toString() {
		String res = "   requires " + requires + "\n   modifies ";
		for (int i = 0; i < modifies.length; i++) {
			if (i != 0)
				res += ",";
			res += modifies[i].toString();
		}
		res += "\n   ensures " + ensures + "\n   exsures ";
		for (int i = 0; i < exsures.length; i++) {
			if (i != 0)
				res += "\n           ";
			res += exsures[i].toString();
		}
		return res;
	}

	/**
	 * @return
	 */
	public String getRequires() {
		return "   requires " + requires;
	}
	/**
	 * @return
	 */
	public String getEnsures() {
		return "   ensures " + ensures;
	}

	/**
	 * @return
	 */
	public String getExsures() {
		String res = "   exsures ";
		for (int i = 0; i < exsures.length; i++) {
			if (i != 0)
				res += "\n           ";
			res += exsures[i].toString();
		}
		return res;
	}

	/**
	 * @return
	 */
	public String getModifies() {
		String res = "   modifies ";
		for (int i = 0; i < modifies.length; i++) {
			if (i != 0)
				res += ",";
			res += modifies[i].toString();
		}
		return res;
	}


}

class Exsures {
	Formula exception_index;
	Formula ex;

	Exsures(DataInput in) throws IOException {
		exception_index = new Formula(in);
		ex = new Formula(in);
	}

	public String toString() {
		return "(" + exception_index + ") " + ex;
	}
}
