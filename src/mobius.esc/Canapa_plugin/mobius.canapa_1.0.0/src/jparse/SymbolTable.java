/*
 * @(#)$Id: SymbolTable.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import java.util.ArrayList;
import java.util.HashMap;
import jparse.expr.VarAST;
import jparse.stmt.StatementAST;

/**
 * A mapping from names to definitions of those names (AST nodes)
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class SymbolTable {

    /**
     * The symbol table for the enclosing scope
     */
    final SymbolTable parent;

    /**
     * The type (class or interface) in which the symbols in this table are
     * defined
     */
    private TypeAST type;

    /**
     * The mapping from variable names to AST nodes representing the
     * definitions of those variables
     */
    private final HashMap varMap = new HashMap();

    /**
     * An alphabetical list of methods (methods with the same name are in no
     * particular order)
     */
    private MethAST[] methods = new MethAST[0];

    /**
     * The mapping from label names to AST nodes representing the labeled
     * statement
     */
    private final HashMap labelMap = new HashMap();

    /**
     * Create a new <code>SymbolTable</code>
     */
    public SymbolTable() {
	parent = JavaAST.currSymTable;
    }

    /**
     * Set the enclosing type for this symbol table
     *
     * @param enclosingType the enclosing type for this symbol table
     */
    void setEnclosingType(final TypeAST enclosingType) {
	type = enclosingType;
    }

    /**
     * Add a variable symbol to the symbol table
     *
     * @param ast the AST node defining the variable
     */
    public void addVar(final VarAST ast) {
	varMap.put(ast.getName(), ast);
    }

    /**
     * Find a variable symbol in the symbol table
     *
     * @param name the name of the variable to look up
     * @return the AST defining <var>name</var>, or <code>null</code> if it
     * cannot be found
     */
    public VarAST getVar(final String name) {
	final Object ret = varMap.get(name);
	return (ret != null)
	    ? (VarAST)ret
	    : ((parent != null) ? parent.getVar(name) : null);
    }

    /**
     * Add a method symbol to the symbol table
     *
     * @param meth the AST node describing the method
     */
    public void addMeth(final MethAST meth) {
	// Find an index where this entry can go in alphabetical order
	int low = 0;
	int high = methods.length - 1;
	while (low <= high) {
	    final int mid = (low + high) / 2;
	    final int compare = meth.compareTo(methods[mid]);
	    if (compare < 0) {
		high = mid - 1;
	    } else if (compare > 0) {
		low = mid + 1;
	    } else {
		low = mid;
		high = mid - 1;
	    }
	}

	// Now make a bigger array, and leave a gap for the new one
	final MethAST[] newMeths = new MethAST[methods.length + 1];
	System.arraycopy(methods, 0, newMeths, 0, low);
	newMeths[low] = meth;
	System.arraycopy(methods, low, newMeths, low+1, methods.length - low);
	methods = newMeths;
    }

    /**
     * Find a method symbol in the symbol table
     *
     * @param name the name of the method to look up
     * @param params the types of the parameters to the method
     * @param caller the type of the caller
     * @return the most closely matching method, or <code>null</code> if one
     * could not be found
     */
    public Method getMeth(final String name, final Type[] params,
			  final Type caller) {
	// If the query is made on a subordinate symbol table, ask the parent
	if (type == null)
	    return parent.getMeth(name, params, caller);

	// Otherwise, get all matching methods
	Method[] matches = getMeths(name, params, caller);

	// If we didn't get a match, then check the interfaces we implement or
	// extend
	if (matches.length == 0) {
	    final Type[] interfaces = type.retrieveType().getInterfaces();
	    for (int i = 0; i < interfaces.length; i++) {
		final Method match =
		    interfaces[i].getMethod(name, params, caller);
		if (match != null) {
		    final Method[] newMatches = new Method[matches.length + 1];
		    System.arraycopy(matches, 0, newMatches, 0,
				     matches.length);
		    newMatches[matches.length] = match;
		    matches = newMatches;
		}
	    }
	}

	// Did we get a match?
	if (matches.length == 0) {
	    return null;
	}

	// Pick the best match
	Method bestMatch = matches[0];
	boolean needBetter = false;
	for (int i = 1; i < matches.length; i++) {
	    Method newMatch = bestMatch.bestMatch(matches[i]);
	    needBetter = newMatch == null;
	    if (newMatch != null)
		bestMatch = newMatch;
	}
	if (needBetter) {
	    System.err.println("There was no best match!\nContenders are:");
	    for (int i = 0; i < matches.length; i++) {
		System.err.println(matches[i].toString());
	    }
	}
	return bestMatch;
    }

    /**
     * Retrieve all matching methods
     *
     * @param name the name of the method to look up
     * @param params the types of the parameters to the method
     * @param caller the type of the caller
     * @return an array containing all matching methods.  If no matching
     * methods are found, an array of length 0 will be returned.
     */
    public Method[] getMeths(final String name, final Type[] params,
			     final Type caller) {
	// Get all methods with the correct name and parameter types from the
	// supertypes
	Method[] matches;
	try {
	    final Type myType = type.retrieveType();
	    final Type superType = myType.isInterface()
		? Type.objectType
		: myType.getSuperclass();
	    matches = superType.getMeths(name, params, caller);
	} catch (ClassNotFoundException classEx) {
	    matches = new Method[0];
	}

	// Find an index where this method name might be stored
	int low = 0;
	int high = methods.length - 1;
	while (low <= high) {
	    final int mid = (low + high) / 2;
	    final int compare = name.compareTo(methods[mid].getName());
	    if (compare < 0) {
		high = mid - 1;
	    } else if (compare > 0) {
		low = mid + 1;
	    } else {
		low = mid;
		high = mid - 1;
	    }
	}

	// Go backwards until we find the first one
	int index;
	for (index = low; index >= 0 && index < methods.length &&
		 name.equals(methods[index].getName()); index--);

	// Now go forwards, adding all candidate methods to the pool
	for (int i = index + 1;
	     i < methods.length && name.equals(methods[i].getName()); i++){
	    if (methods[i].match(params, caller)) {
		final Method[] newMatches = new Method[matches.length + 1];
		System.arraycopy(matches, 0, newMatches, 0, matches.length);
		newMatches[matches.length] = methods[i];
		matches = newMatches;
	    }
	}

	return matches;
    }

    /**
     * Retrieve all methods defined by this symbol table
     *
     * @return an array of methods.  If no methods are defined in this symbol
     * table, an array of length 0 is returned.
     */
    public Method[] getMeths() {
	return methods;
    }

    /**
     * Add a labeled statement to the symbol table
     *
     * @param label the label on the statement
     * @param stmt the AST node for the labeled statement
     */
    public void addLabel(final String label, final JavaAST stmt) {
	labelMap.put(label, stmt);
    }

    /**
     * Find a labeled statement in the symbol table
     *
     * @param label the label to look up
     * @return the AST for the statement with label <var>label</var>, or
     * <code>null</code> if it cannot be found
     */
    public StatementAST getLabel(final String label) {
	final Object ret = labelMap.get(label);
	return (ret != null)
	    ? (StatementAST)ret
	    : ((parent != null) ? parent.getLabel(label) : null);
    }

    public String toString() {
	final StringBuffer buf = new StringBuffer("Symbol Table:\n");
	if (!varMap.isEmpty()) {
	    buf.append("** Variables **\n");
	    buf.append(varMap.toString());
	    buf.append('\n');
	}
	if (methods.length > 0) {
	    buf.append("** Methods **\n");
	    for (int i = 0; i < methods.length; i++) {
		buf.append(methods[i].toString());
		buf.append('\n');
	    }
	}
	if (!labelMap.isEmpty()) {
	    buf.append("** Labels **\n");
	    buf.append(labelMap.toString());
	    buf.append('\n');
	}
	if (parent != null) {
	    buf.append(parent.toString());
	}
	return buf.toString();
    }
}
