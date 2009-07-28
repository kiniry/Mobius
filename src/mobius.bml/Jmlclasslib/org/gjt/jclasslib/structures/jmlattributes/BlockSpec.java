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
public class BlockSpec {

	short StartIndex;
	short EndIndex;
	Formula requires;
	Formula[] modifies;
	Formula ensures;

	BlockSpec(DataInput in) throws IOException {
		StartIndex = (short) in.readUnsignedShort();
		EndIndex = (short) in.readUnsignedShort();
		requires = new Formula(in);
		modifies = new Formula[in.readUnsignedShort()];
		for (int i = 0; i < modifies.length; i++)
			modifies[i] = new Formula(in);
		ensures = new Formula(in);
	}

	public String toString() {
		String res = "@" + StartIndex + ";" + EndIndex + ":   modifies ";
		for (int i = 0; i < modifies.length; i++) {
			if (i != 0)
				res += ",";
			res += modifies[i].toString();
		}
		res += "\n   requires " + requires + "\n   ensures " + ensures + "\n";
		return res;
	}

	/**
	 * @return
	 */
	public String getStartIndex() {
		return "Start index: " + StartIndex;
	}
	/**
	 * @return
	 */
	public String getEndIndex() {
		return "End index: " + EndIndex;
	}

	/**
	 * @return
	 */
	public String getEnsures() {
		return "ensures " + ensures;
	}

	/**
	 * @return
	 */
	public String getModifies() {
		String res = "modifies ";
		for (int i = 0; i < modifies.length; i++) {
			if (i != 0)
				res += ",";
			res += modifies[i].toString();
		}
		return res;
	}

	/**
	 * @return
	 */
	public String getRequires() {
		return "requires " + requires;
	}


}
