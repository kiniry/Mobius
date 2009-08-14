/*
 * @(#)$Id: FileAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
 *
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
package jparse;

import antlr.CommonHiddenStreamToken;
import java.io.File;
import java.io.OutputStreamWriter;
import java.util.HashMap;

/**
 * An AST node that represents the contents of a file
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class FileAST extends JavaAST implements JavaTokenTypes {

    /**
     * The file currently being evaluated
     */
    static FileAST currFile;

    /**
     * The file that was parsed to create this AST
     */
    final File theFile;

    /**
     * The package for this file, or <code>null</code> for the default package
     */
    String pkg;

    /**
     * The import statements for this file
     */
    String[] imports;

    /**
     * The top-level class and interface definitions for this file
     */
    TypeAST[] types;

    /**
     * A mapping from class names to types, in the context of the import list
     * for this file
     */
    private final HashMap map = new HashMap();

    /**
     * Create a new file AST node
     *
     * @param file the file parsed to create this AST
     */
    public FileAST(final File file) {
	super();
	initialize(FILE, "");
	theFile = file;

	// Seed the map with the primitive data types
	map.put("boolean", Type.booleanType);
	map.put("byte",	   Type.byteType   );
	map.put("char",	   Type.charType   );
	map.put("double",  Type.doubleType );
	map.put("float",   Type.floatType  );
	map.put("int",	   Type.intType    );
	map.put("long",	   Type.longType   );
	map.put("short",   Type.shortType  );
	map.put("void",	   Type.voidType   );
    }

    /**
     * Set the initial hidden token for the file.  This ensures that leading
     * comments and whitespace are printed during a tree traversal.
     *
     * @param hiddenTok the initial hidden token
     */
    void setInitialHiddenToken(final CommonHiddenStreamToken hiddenTok) {
	hiddenAfter = hiddenTok;
    }

    /**
     * Find a type with the given name, using the import list for this file
     *
     * @param name the name of the type to look up
     * @return a type object representing this type
     * @exception ClassNotFoundException if the class cannot be found
     */
    public Type getType(final String name) throws ClassNotFoundException {
	// Case 1: we have looked up this name before
	Type type = (Type)map.get(name);
	if (type != null) {
	    return type;
	}

	// Case 2: it is an array; look up the base type
	if (name.endsWith("[]")) {
	    try {
		final int index = name.indexOf('[');
		final Type baseType = getType(name.substring(0, index));
		if (baseType == null) {
		    System.err.print("**** Failed to resolve ");
		    System.err.println(name.substring(0, index));
		}
		type =
		    Type.forName(baseType.getName() + name.substring(index));
		map.put(name, type);
		return type;
	    } catch (ClassNotFoundException ex0) {
	    }
	}

	// Case 3: it is a fully qualified name, or a partially qualified
	// inner class
	final int index = name.lastIndexOf('.');
	if (index != -1) {
	    // First see if it is a fully qualified name
	    try {
		type = Type.forName(name);
		map.put(name, type);
		return type;
	    } catch (ClassNotFoundException ex1) {
		// Now see if it is a partially qualified inner class
		try {
		    final Type t = getType(name.substring(0, index));
		    type = t.getInner('$' + name.substring(index + 1));
		    if (type != null) {
			map.put(name, type);
			return type;
		    }
		} catch (ClassNotFoundException ex2) {
		}
	    }
	}

	// Case 4: it is an unqualified inner class in this file
	final String dollarName = '$' + name;
	for (int i = 0; i < types.length; i++) {
	    final TypeAST[] inner = types[i].inner;
	    for (int j = 0; j < inner.length; j++) {
		if (inner[j].name.endsWith(dollarName)) {
		    type = inner[j].retrieveType();
		    map.put(name, type);
		    return type;
		}
	    }
	}

	// Case 5: it is in the same package
	final String dotName = '.' + name;
	try {
	    type = Type.forName(pkg + dotName);
	    map.put(name, type);
	    return type;
	} catch (ClassNotFoundException ex3) {
	}

	// Case 6: it is in the java.lang package
	try {
	    type = Type.forName("java.lang." + name);
	    map.put(name, type);
	    return type;
	} catch (ClassNotFoundException ex4) {
	}

	// Case 7: it is an imported class
	for (int i = 0; i < imports.length; i++) {
	    String fullName;
	    final int lastIndex = imports[i].length() - 1;
	    if (imports[i].charAt(lastIndex) == '*') {
		fullName = imports[i].substring(0, lastIndex) + name;
	    } else if (imports[i].endsWith(dotName)) {
		fullName = imports[i];
	    } else {
		continue;
	    }

	    try {
		type = Type.forName(fullName);
		map.put(name, type);
		return type;
	    } catch (ClassNotFoundException ex5) {
	    }
	}

	// Case 8: it is a class in the default package
	try {
	    type = Type.forName(name);
	    map.put(name, type);
	    return type;
	} catch (ClassNotFoundException ex6) {
	}

	// Case 9: it is an unqualified inner class in a superclass of some
	// class in this file
	for (int i = 0; i < types.length; i++) {
	    type = types[i].retrieveType().getInner(dollarName);
	    if (type != null) {
		map.put(name, type);
		return type;
	    }
	}

	// Case 10: it is an unqualified inner class in an imported class
	for (int i = 0; i < imports.length; i++) {
	    final int lastIndex = imports[i].length() - 1;
	    if (imports[i].charAt(lastIndex) != '*') {
		try {
		    final Type t = Type.forName(imports[i]);
		    type = t.getInner(dollarName);
		    if (type != null) {
			map.put(name, type);
			return type;
		    }
		} catch (ClassNotFoundException ex7) {
		}
	    }
	}

	// Nope, couldn't find it
	throw new ClassNotFoundException(name);
    }

    public void parseComplete() {
	for (int i = 0; i < types.length; i++) {
	    types[i].parseComplete();
	}
    }

    public String toString() {
	return theFile.toString();
    }


}
