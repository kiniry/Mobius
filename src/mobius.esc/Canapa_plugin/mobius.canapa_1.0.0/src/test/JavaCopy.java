/*
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Author: Jerry James
 * Email: james@eecs.ku.edu, james@ittc.ku.edu, jamesj@acm.org
 * Address: EECS Department - University of Kansas
 *          Eaton Hall
 *          1520 W 15th St, Room 2001
 *          Lawrence, KS  66045-7621
 */
package test;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;

import jparse.FileAST;
import jparse.Type;
import canapa.util.FakeLocation;
import canapa.util.FixLocation;
import canapa.util.TreeWalker;

/**
 * Copy a Java file by reading it in, parsing it, and walking the parse tree
 * 
 * @version $Revision: 1.5 $, $Date: 2004/07/09 17:32:14 $
 * @author Jerry James
 */
public final class JavaCopy {

	/**
	 * Start the copying program
	 * 
	 * @param args
	 *            command line arguments
	 * @throws java.io.UnsupportedEncodingException
	 *             if the ISO8859-1 encoding is not supported by your platform
	 */
	public static void main(final String[] args)
			throws UnsupportedEncodingException {
		if (args.length == 0) {
			System.err.println("Usage: java JavaCopy filename.java");
			return;
		}

		final OutputStreamWriter out = new OutputStreamWriter(System.out,
				"ISO8859-1");
		final JavaPrinter printer = new JavaPrinter();
		for (int i = 0; i < args.length; i++) {
			try {
				// Ask the type manager to parse the file and give us the AST
				final FileAST tree = Type.parseFile(args[i]);

				// Walk the tree
				//tree.print(out);
				TreeWalker tw = new TreeWalker(tree);
				FixLocation loc = new FakeLocation();
				boolean znalazl = tw.setAtParamNode(loc);
				if (znalazl)
					tw.insertJMLbefore(loc.getSuggestion());
				else
					out.write("WAAAAAAAA!!");
				out.write("ELLO3\n");
				tree.wypiszSie(out);
				out.write("ELLO2\n");
				out.flush();
				out.write("####################################\n");
				printer.compilationUnit(tree, out);
			} catch (Exception ex) {
				try {
					out.flush();
				} catch (IOException ioEx) {
					// Ignored
				}
				ex.printStackTrace();
			}
		}
	}
}
