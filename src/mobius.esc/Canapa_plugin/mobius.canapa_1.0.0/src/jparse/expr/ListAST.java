/*
 * @(#)$Id: ListAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import java.util.ArrayList;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents an expression list
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class ListAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The list of expressions
     */
    private final ExpressionAST[] list;

    /**
     * The types of the expressions in this expression list
     */
    private Type[] types;

    /**
     * Create a new expression list AST
     *
     * @param firstExpr the first expression in the list
     */
    public ListAST(final AST firstExpr) {
	super();
	initialize(ELIST, "ELIST");
	final ArrayList theList = new ArrayList();
	for (AST a = firstExpr; a != null; a = a.getNextSibling()) {
	    theList.add(a);
	    a = a.getNextSibling();	// Skip the comma
	    if (a == null)
		break;
	}
	list = new ExpressionAST[theList.size()];
	theList.toArray(list);
    }

    public void parseComplete() {
	for (int i = 0; i < list.length; i++) {
	    list[i].parseComplete();
	}
    }

    protected Type computeType() {
	// Make the type array
	types = new Type[list.length];
	for (int i = 0; i < list.length; i++) {
	    types[i] = list[i].retrieveType();
	}

	// The type of an expression list is the type of its rightmost
	// expression
	return (types.length == 0) ? null : types[types.length - 1];
    }

    protected Type[] computeExceptions() {
	Type[] retVal = noTypes;
	for (int i = 0; i < list.length; i++) {
	    retVal = Type.mergeTypeLists(retVal, list[i].getExceptionTypes());
	}
	return retVal;
    }

    protected Object computeValue() {
	return (list.length > 0)
	    ? list[list.length - 1].getValue()
	    : nonconstant;
    }

    public VarList getVarList() {
	final VarList[] lists = new VarList[list.length];
	for (int i = 0; i < list.length; i++) {
	    lists[i] = list[i].getVarList();
	}
	return new VarList(lists);
    }

    /**
     * Get the list of expressions
     *
     * @return an array containing the expressions in the list, in order
     */
    public ExpressionAST[] getList() {
	return list;
    }

    /**
     * Get a list of all the types in this expression list (used for parameter
     * lists)
     *
     * @return an array containing one type for expression in this list, in
     * order
     */
    public Type[] getTypes() {
	if (types == null)
	    retrieveType();	// Don't need the return value
	return types;
    }

    public String toString() {
	final Type[] types = getTypes();

	final StringBuffer buf = new StringBuffer();
	for (int i = 0; i < types.length - 1; i++) {
	    buf.append(types[i].getName());
	    buf.append(',');
	}
	if (types.length > 0)
	    buf.append(types[types.length - 1].getName());
	return buf.toString();
    }
}
