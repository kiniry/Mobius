/*
 * Created on 2005-11-01
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

import java.io.IOException;
import java.io.OutputStreamWriter;

/**
 * @author Admin
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class PPrinter {
	private int indent = 0;
	public void incIndent() {
		indent++;
	}
	public void decIndent() {
		indent--;
	}
	public void print(OutputStreamWriter output) {
		String s = "";
		for (int i = 0; i < indent; i++)
			s += "\t";
		try {
			output.write(s);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
