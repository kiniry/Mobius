/*
 * @(#)$Id: IdentifierAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
package jparse.expr;

import antlr.Token;
import jparse.JavaAST;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents an identifier
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public class IdentifierAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The full name of this identifier
     */
    private String name;

    /**
     * <code>true</code> if this is a method name
     */
    private boolean isMethod = false;

    /**
     * Create a new identifier AST
     */
    public IdentifierAST() {
	super();
    }

    /**
     * Create a new identifier AST
     *
     * @param token the token represented by this AST node
     */
    public IdentifierAST(final Token token) {
	super(token);
	name = getText();
    }

    /**
     * Set the name of this identifier
     *
     * @param theName the name of this identifier
     */
    public final void setName(String theName) {
	name = theName;
    }

    /**
     * Extract the full name of this identifier, even if is is a dotted name
     *
     * @return the concatenated string representing the full name of the
     * identifier
     */
    public final String getName() {
	return name;
    }

    /**
     * Identify this as a method name
     */
    public final void setMethod() {
	isMethod = true;
    }

    /**
     * Compares this identifier with another for order.
     *
     * @param ident the <code>IdentifierAST</code> to compare with this one
     * @return a negative integer, zero, or a positive integer as this object
     * is less than, equal to, or greater than the specified
     * <code>IdentifierAST</code>
     */
    public int compareTo(final IdentifierAST ident) {
	return name.compareTo(ident.name);
    }

    protected Type computeType() {
	// If my first child has a type, then this is a dot, followed by a
	// variable or method name, "this", "super", or "class".
	final ExpressionAST firstChild = (ExpressionAST)getFirstChild();
	if (firstChild != null) {
	    final Type childType = firstChild.retrieveType();
	    if (childType != null) {
		// FIXME: Need to check accessibility
		switch (firstChild.getNextSibling().getType()) {
		case LITERAL_class:
		    return Type.forClass(Class.class);		// JLS 15.8.2
		case LITERAL_this:
		    return childType;				// JLS 15.8.4
		case LITERAL_super:
		    try {
			return childType.getDeclaringClass().getSuperclass();
		    } catch (ClassNotFoundException classEx) {
			return null;
		    }
		default:
		    if (isMethod)
			return childType;

		    // Have to check for arrays specially
		    final String nextText =
			firstChild.getNextSibling().getText();
		    if (nextText.equals("length") &&
			childType.getComponentType() != null)
			return Type.intType;

		    final Type varType = childType.varType(nextText);
		    if (varType != null)
			return varType;
		}
	    }
	}

	// If there is no dot, this might be a variable name, "this", or
	// "super"
	final int lastDot = name.lastIndexOf('.');
	if (lastDot < 0) {
	    final Type myType = typeAST.retrieveType();
	    switch (getType()) {
	    case LITERAL_this:
		return myType.getDeclaringClass();
	    case LITERAL_super:
		try {
		    return topLevel.getType(typeAST.getSuperclass());
		} catch (ClassNotFoundException classEx) {
		    return null;
		}
	    default:
		// Is it a local variable?
		final VarAST varAST = symTable.getVar(name);
		if (varAST != null) {
		    return varAST.retrieveType();
		}

		// Is it a field?
		final Type varType = myType.varType(name);
		if (varType != null) {
		    return varType;
		}

		// Is it a field of an enclosing type?
		final Type outerType = myType.getDeclaringClass();
		if (outerType != null) {
		    final Type varType2 = outerType.varType(name);
		    if (varType2 != null) {
			return varType2;
		    }
		}
	    }
	}

	// Otherwise, this might be a type name
	try {
	    return topLevel.getType(name);
	} catch (ClassNotFoundException classEx) {
	    // Or, it is a partial name.  Wait until we get the rest.
	    return null;
	}
    }

    protected Type[] computeExceptions() {
	return noTypes;
    }

    protected Object computeValue() {
	final VarAST var = symTable.getVar(name);
	return (var == null) ? nonconstant : var.getValue();
    }

    public VarList getVarList() {
	return new VarList(symTable.getVar(name));
    }

    public String toString() {
	return name;
    }
}
