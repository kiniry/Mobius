/*
 * @(#)$Id: ArrayInitAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents an array initializer
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ArrayInitAST extends ExpressionAST
    implements JavaTokenTypes {

    /**
     * The base type of the array being initialized
     */
    private TypeAST baseType;

    /**
     * The list of initializers
     */
    private ExpressionAST[] initializers;

    /**
     * The dimension of this array initializer
     */
    private int dim;

    /**
     * Create a new array initializer AST
     *
     * @param token the token represented by this AST node
     */
    public ArrayInitAST(final Token token) {
	super(token);
	setType(ARRAY_INIT);
    }

    public void parseComplete() {
	// Set the base type
	baseType = context.type;

	// Set up the initializers array
	final ArrayList list = new ArrayList();
	for (AST a = getFirstChild(); a != null && a.getType() != RCURLY;
	     a = a.getFirstChild()) {
	    list.add(a);
	    a = a.getNextSibling();
	    if (a == null || a.getType() != COMMA)
		break;
	}
	initializers = new ExpressionAST[list.size()];
	list.toArray(initializers);

	// Complete the initializers
	for (int i = 0; i < initializers.length; i++) {
	    initializers[i].parseComplete();
	}
    }

    protected Type computeType() {
	final Type bType = baseType.retrieveType();
	for (int i = 0; i < initializers.length; i++) {
	    if (initializers[i] instanceof ArrayInitAST) {
		final ArrayInitAST init = (ArrayInitAST)initializers[i];
		if (init.dim > dim)
		    dim = init.dim;
	    }
	}
	dim++;
	final String bTypeName = bType.getName();
	final int index = bTypeName.indexOf('[');
	try {
	    return Type.forName(bTypeName.substring(0, index + 2 * dim));
	} catch (Exception ex) {
	    return null;
	}
    }

    protected Type[] computeExceptions() {
	Type[] e = noTypes;
	for (int i = 0; i < initializers.length; i++) {
	    e = Type.mergeTypeLists(e, initializers[i].getExceptionTypes());
	}
	return e;
    }

    protected Object computeValue() {
	// These can't be used as constant expressions, so don't bother trying
	return nonconstant;
    }

    public VarList getVarList() {
	final VarList[] lists = new VarList[initializers.length];
	for (int i = 0; i < initializers.length; i++) {
	    lists[i] = initializers[i].getVarList();
	}
	return new VarList(lists);
    }

    /**
     * Get the list of initializers
     *
     * @return an array containing the initializers
     */
    public ExpressionAST[] getInitializers() {
	return initializers;
    }
}
