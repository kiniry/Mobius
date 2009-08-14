/*
 * @(#)$Id: NumLiteralAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a literal number
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class NumLiteralAST extends ExpressionAST {

    /**
     * Create a new literal number AST
     *
     * @param token the token represented by this AST node
     */
    public NumLiteralAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	final String tokenString = (context.negative)
	    ? "-" + getText() : getText();
	final int length = tokenString.length();
	final char lastChar = tokenString.charAt(length - 1);
	final boolean intLiteral = lastChar != 'l' && lastChar != 'L';
	type = intLiteral ? Type.intType : Type.longType;	// JLS 15.8.1
	final boolean decimal = tokenString.length() <= 2 ||
	    tokenString.charAt(0) != '0' ||
	    Character.toUpperCase(tokenString.charAt(1)) != 'X';
	final String numString =
	    tokenString.substring(decimal ? 0 : 2,
				  intLiteral ? length : length - 1);
	try {
	    value = intLiteral
		? (Object)Integer.valueOf(numString, decimal ? 10 : 16)
		: (Object)Long.valueOf(numString, decimal ? 10 : 16);
	} catch (NumberFormatException numEx) {
	    // This can mean many things.  One thing it can mean is that we
	    // have seen a hexadecimal value that is too large to fit into a
	    // positive int/long (i.e., it is a negative value).  We will have
	    // to build up the value digit by digit.
	    long theVal = 0L;
	    for (int i = 0; i < numString.length(); i++) {
		final char c = numString.charAt(i);
		theVal <<= 4;
		if (c >= '0' && c <= '9')
		    theVal += c - '0';
		else if (c >= 'A' && c <= 'F')
		    theVal += c - 'A' + 10;
		else if (c >= 'a' && c <= 'f')
		    theVal += c - 'a' + 10;
		else
		    throw numEx;
	    }
	    value = intLiteral
		? (Object)new Integer((int)theVal)
		: (Object)new Long(theVal);
	}
    }

    protected Type computeType() {
        return type;
    }

    protected Type[] computeExceptions() {
	return noTypes;
    }

    protected Object computeValue() {
	return value;
    }

    public VarList getVarList() {
	return new VarList();
    }
}
