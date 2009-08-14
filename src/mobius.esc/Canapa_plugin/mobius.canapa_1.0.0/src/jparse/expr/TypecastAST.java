/*
 * @(#)$Id: TypecastAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a typecast
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class TypecastAST extends ExpressionAST
    implements JavaTokenTypes {

    /**
     * The type to cast to
     */
    private TypeAST castType;
     
    /**
     * The expression to cast
     */
    private ExpressionAST castExpr;

    /**
     * Create a new typecast AST
     *
     * @param token the token represented by this AST node
     */
    public TypecastAST(final Token token) {
	super(token);
	setType(TYPECAST);
    }

    public void parseComplete() {
	castType = (TypeAST)getFirstChild();
	castExpr = (ExpressionAST)castType.getNextSibling().getNextSibling();
	castType.parseComplete();
	context.negative = false;
	castExpr.parseComplete();
    }

    protected Type computeType() {
	// See JLS 15.16
	return castType.retrieveType();
    }

    protected Type[] computeExceptions() {
	// ClassCastException is not checked
	return castExpr.getExceptionTypes();
    }

    protected Object computeValue() {
	final Object castVal = castExpr.getValue();
	if (!(castVal instanceof Number))
	    return castVal;

	// It's a number.  Create a new wrapper of the appropriate type.
	final Number num = (Number)castVal;
	final Type theType = castType.retrieveType();
	if (theType == Type.byteType)
	    return new Byte(num.byteValue());
	if (theType == Type.shortType)
	    return new Short(num.shortValue());
	if (theType == Type.intType)
	    return new Integer(num.intValue());
	if (theType == Type.longType)
	    return new Long(num.longValue());
	if (theType == Type.floatType)
	    return new Float(num.floatValue());
	return new Double(num.doubleValue());
    }

    public VarList getVarList() {
	return castExpr.getVarList();
    }

    /**
     * Get the name of the type to cast to
     *
     * @return the cast type name
     */
    public TypeAST getTypeName() {
	return castType;
    }

    /**
     * Get the expression to be typecast
     *
     * @return the expression whose type is to be cast
     */
    public ExpressionAST getCastExpression() {
	return castExpr;
    }

    public String toString() {
	return '(' + castType.toString() + ')';
    }
}
