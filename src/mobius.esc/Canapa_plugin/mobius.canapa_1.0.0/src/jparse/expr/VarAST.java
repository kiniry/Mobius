/*
 * @(#)$Id: VarAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import antlr.collections.AST;
import jparse.*;

/**
 * An AST node that represents a variable definition or formal parameter
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class VarAST extends IdentifierAST implements JavaTokenTypes {

    /**
     * The modifiers for this variable
     */
    private ModifierAST mods;

    /**
     * The declared type of this variable
     */
    private TypeAST declType;

    /**
     * Any trailing array brackets on the declaration
     */
    private JavaAST brackets;

    /**
     * The initializer (if any) for this variable
     */
    private InitializerAST initializer;

    /**
     * <code>true</code> if this is a field (static or instance variable);
     * <code>false</code> if this is a local variable (including parameters)
     */
    private boolean field;

    /**
     * Create a new variable AST
     *
     * @param token the token represented by this AST node
     */
    public VarAST(final Token token) {
	super(token);

	// Register this variable with the symbol table
	symTable.addVar(this);
    }

    public void parseComplete() {
	mods = context.mods;
	declType = context.type;
	AST a = getNextSibling();
	if (a != null && a.getType() == ARRAY_DECLARATOR) {
	    brackets = (JavaAST)a;
	    do {
		a = a.getNextSibling().getNextSibling();
	    } while (a != null && a.getType() == ARRAY_DECLARATOR);
	}
	if (a != null && a instanceof InitializerAST) {
	    initializer = (InitializerAST)a;
	    initializer.parseComplete();
	}
	field = context.isField;
    }

    protected Type computeType() {
	final Type baseType = declType.retrieveType();
	if (brackets == null) {
	    return baseType;
	}
	final StringBuffer buf = new StringBuffer(baseType.getName());
	for (AST b = brackets; b != null && b.getType() == ARRAY_DECLARATOR;
	     b = b.getNextSibling().getNextSibling())
	    buf.append("[]");
	try {
	    return Type.forName(buf.toString());
	} catch (ClassNotFoundException classEx) {
	    return null;
	}
    }

    protected Type[] computeExceptions() {
	return (initializer == null)
	    ? noTypes
	    : initializer.getExceptionTypes();
    }

    protected Object computeValue() {
	return (mods.isFinal() || initializer == null)
	    ? nonconstant
	    : initializer.getValue();
    }

    public VarList getVarList() {
	final VarList thisVar = new VarList(this);
	return (initializer == null)
	    ? thisVar
	    : new VarList(thisVar, initializer.getVarList());
    }

    /**
     * Get the modifiers for this variable
     *
     * @return the modifiers
     */
    public ModifierAST getModifiers() {
	return mods;
    }

    /**
     * Get the name of the declared type for this variable
     *
     * @return the type name
     */
    public TypeAST getTypeName() {
	return declType;
    }

    /**
     * Get the brackets modifying the type name, if those brackets follow the
     * variable name
     *
     * @return brackets modifying the type name, or <code>null</code> if there
     * are none
     */
    public JavaAST getBrackets() {
	return brackets;
    }

    /**
     * Get the initializer for this variable
     *
     * @return the initializer for this variable, or <code>null</code> if
     * there is not one
     */
    public InitializerAST getInitializer() {
	return initializer;
    }

    /**
     * Determine whether this variable is a field (static or instance
     * variable) or a local variable or parameter
     *
     * @return <code>true</code> if this variable is a field;
     * <code>false</code> otherwise
     */
    public boolean isField() {
	return field;
    }

    public String toString() {
	final StringBuffer buf = new StringBuffer(declType.toString());
	buf.append(' ');
	buf.append(super.toString());
	for (AST b = brackets; b != null && b.getType() == ARRAY_DECLARATOR;
	     b = b.getNextSibling().getNextSibling())
	    buf.append("[]");
	return buf.toString();
    }
}
