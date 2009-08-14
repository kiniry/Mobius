/*
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
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

import java.io.*;
import jparse.FileAST;
import jparse.Type;

/**
 * Print out the types of all expressions in a Java file
 *
 * @version $Revision: 1.5 $, $Date: 2004/07/09 17:32:14 $
 * @author Jerry James
 */
public final class JavaType {

    /**
     * Start the typing program
     *
     * @param args command line arguments
     * @throws java.io.UnsupportedEncodingException if the ISO8859-1 encoding
     * is not supported by your platform
     */
    public static void main(final String[] args)
	throws UnsupportedEncodingException {
	if (args.length == 0) {
	    System.err.println("Usage: java JavaType file1.java file2.java ...");
	    return;
	}

	// Parse all of the input files
	final FileAST[] tree = new FileAST[args.length];
	for (int i = 0; i < args.length; i++) {
	    try {
		// Ask the type manager to parse the file and give us the AST
		tree[i] = Type.parseFile(args[i]);
	    } catch (Exception ex) {
		ex.printStackTrace();
	    }
	}

	// Create an output stream
	final OutputStreamWriter out = new OutputStreamWriter(System.out,
							      "ISO8859-1");
	final JavaTyper typer = new JavaTyper();
	for (int i = 0; i < args.length; i++) {
	    if (tree[i] != null) {
		System.err.println("\n**** Examining types and exceptions for "
				   + args[i] + " ****");
		try {
		    // Walk the tree, printing expression types
		    typer.compilationUnit(tree[i], out);
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
	try {
	    out.write('\n');
	} catch (IOException ioEx) {
	    // Ignored
	}
    }
}
