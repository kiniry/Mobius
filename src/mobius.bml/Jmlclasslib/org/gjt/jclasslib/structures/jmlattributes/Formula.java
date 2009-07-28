/*
 * Created on May 26, 2004
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
public class Formula {

	String text;

	Formula(DataInput in) throws IOException {
		Formula f1;
		Formula f2;
		byte n;
		byte node = in.readByte();
		switch (node) {
			case 0x00 :
				text = "true";
				break;
			case 0x01 :
				text = "false";
				break;
			case 0x02 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " && " + f2.text;
				break;
			case 0x03 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " || " + f2.text;
				break;
			case 0x04 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " ==> " + f2.text;
				break;
			case 0x05 :
				f1 = new Formula(in);
				text = "! " + f1.text;
				break;
			case 0x06 :
				text = "(\\forall ";
				n = in.readByte();
				for (int i = 0; i < n; i++)
					text += new Formula(in);
				text += ";" + new Formula(in) + ")";
				break;
			case 0x07 :
				text = "(\\exists ";
				n = in.readByte();
				for (int i = 0; i < n; i++)
					text += new Formula(in);
				text += ";" + new Formula(in) + ")";
				break;
			case 0x10 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " == " + f2.text;
				break;
			case 0x11 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " > " + f2.text;
				break;
			case 0x12 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " < " + f2.text;
				break;
			case 0x13 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " <= " + f2.text;
				break;
			case 0x14 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " >= " + f2.text;
				break;
			case 0x15 :
				text = new Formula(in) + " instanceof" + new Formula(in);
				break;
			case 0x16 :
				text = new Formula(in) + " <: " + new Formula(in);
				break;
			case 0x17 :
				f1 = new Formula(in);
				f2 = new Formula(in);
				text = f1.text + " != " + f2.text;
				break;
			case 0x20 :
				text = new Formula(in) + " + " + new Formula(in);
				break;
			case 0x21 :
				text = new Formula(in) + " - " + new Formula(in);
				break;
			case 0x22 :
				text = new Formula(in) + " * " + new Formula(in);
				break;
			case 0x23 :
				text = new Formula(in) + " / " + new Formula(in);
				break;
			case 0x24 :
				text = new Formula(in) + " % " + new Formula(in);
				break;
			case 0x25 :
				text = "- " + new Formula(in);
				break;
			case 0x30 :
				text = new Formula(in) + " & " + new Formula(in);
				break;
			case 0x31 :
				text = new Formula(in) + " | " + new Formula(in);
				break;
			case 0x32 :
				text = new Formula(in) + " ^ " + new Formula(in);
				break;
			case 0x33 :
				text = new Formula(in) + " << " + new Formula(in);
				break;
			case 0x34 :
				text = new Formula(in) + " >> " + new Formula(in);
				break;
			case 0x35 :
				text = new Formula(in) + " >>> " + new Formula(in);
				break;
			case 0x40 :
				text = "" + in.readInt();
				break;
			case 0x41 :
				text = "" + new Character(in.readChar());
				break;
			case 0x50 :
				text = "\\typeof" + new Formula(in) + ")";
				break;
			case 0x51 :
				text = "\\elemtype" + new Formula(in) + ")";
				break;
			case 0x52 :
				text = "\\result";
				break;
			case 0x55 :
				text = "\\Type";
				break;
			case 0x56 :
				text = "length";
				break;
			case 0x60 :
				text = new Formula(in) + "(";
				n = in.readByte();
				for (int i = 0; i < n; i++) {
					if (i != 0)
						text += ",";
					text += new Formula(in);
				}
				text += ")";
				break;
			case 0x61 :
				text = new Formula(in) + "[" + new Formula(in) + "]";
				break;
			case 0x62 :
				text = "(" + new Formula(in) + ") " + new Formula(in);
				break;
			case 0x63 :
				text = new Formula(in) + "." + new Formula(in);
				break;
			case 0x64 :
				text =
					new Formula(in)
						+ "?"
						+ new Formula(in)
						+ ":"
						+ new Formula(in);
				break;
			case 0x70 :
				text = "this";
				break;
			case 0x71 :
				text = "\\old(this)";
				break;
			case 0x72 :
				text = "null";
				break;
			case (byte) 0x80 :
				text = "#" + in.readUnsignedShort();
				break;
			case (byte) 0x81 :
				text = "\\old(#" + in.readUnsignedShort() + ")";
				break;
			case (byte) 0x90 :
				text = "local(" + in.readUnsignedShort() + ")";
				break;
			case (byte) 0x91 :
				text = "\\old(local(" + in.readUnsignedShort() + "))";
				break;
			case (byte) 0xA0 :
				text = "#" + in.readUnsignedShort();
				break;
			case (byte) 0xA1 :
				text = "\\old(#" + in.readUnsignedShort() + ")";
				break;
			case (byte) 0xB0 :
				text = "#" + in.readUnsignedShort();
				break;
			case (byte) 0xC0 :
				text = "#" + in.readUnsignedShort();
				break;
			case (byte) 0xD0 :
				text = "\\everything";
				break;
			case (byte) 0xD1 :
				text = "\\nothing";
				break;
			case (byte) 0xD2 :
				text = new Formula(in).toString();
				break;
			case (byte) 0xD3 :
				text = new Formula(in) + "." + new Formula(in);
				break;
			case (byte) 0xD4 :
				text = new Formula(in) + "[" + new Formula(in) + "]";
				break;
			case (byte) 0xD5 :
				text = new Formula(in).toString();
				break;
			case (byte) 0xD6 :
				text = new Formula(in) + ".." + new Formula(in);
				break;
			case (byte) 0xD7 :
				text = "..";
				break;
			case (byte) 0xE0 :
				text = "bv(" + in.readUnsignedShort() + ")";
				break;
			default :
				text = "Error:" + node;
		}
	}

	public String toString() {
		return text;
	}

}
