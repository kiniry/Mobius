/*
 * @(#)$Id: NewAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import java.lang.reflect.Modifier;
import jparse.*;

/**
 * An AST node that represents a "new" expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class NewAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The type to instantiate
     */
    private IdentifierAST typeName;

    /**
     * If this is a new anonymous type, this is the AST for the anonymous
     * class
     */
    private jparse.TypeAST anonymous;

    /**
     * If this is a new array expression, this is the number of dimensions in
     * the array
     */
    private int dimensions;

    /**
     * The parameters, for an object constructor
     */
    private ListAST parameters;

    /**
     * The constructor being accessed by this use of <code>new</code>
     */
    private Constructor theCons;

    /**
     * Create a new "new" expression AST
     *
     * @param token the token represented by this AST node
     */
    public NewAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	typeName = (IdentifierAST)getFirstChild();
	final AST a = typeName.getNextSibling();
	if (a.getType() == LPAREN) {
	    // An object type
	    parameters = (ListAST)a.getNextSibling();
	    parameters.parseComplete();
	    final AST anon = parameters.getNextSibling().getNextSibling();
	    if (anon != null) {
		anonymous = (jparse.TypeAST)anon;
		anonymous.parseComplete();
	    }
	} else {
	    // An array type ... count the dimensions
	    int i;
	    AST b = a;
	    for (i = 0; b != null && b.getType() == ARRAY_DECLARATOR; i++) {
		b = b.getFirstChild();
		final AST c = b.getNextSibling();
		if (c != null) {
		    ((JavaAST)c).parseComplete();
		}
	    }
	    if (b != null) {
		((JavaAST)b).parseComplete();
	    }

	    dimensions = i;
	    b = a.getNextSibling();
	    if (b != null) {
		// There is an array initializer
		context.type = new TypeAST(typeName.getName());
		((ArrayInitAST)b).parseComplete();
	    }
	}
    }

    protected Type computeType() {
	final Type type;
	if (anonymous == null) {
	    type = typeName.retrieveType();
	} else {
	    type = anonymous.retrieveType();
	    ((SourceType)type).anonCheckSuper();
	}

	// If creating an object, find the constructor
	if (dimensions == 0) {
	    final Type myType = typeAST.retrieveType();

	    final Type[] paramTypes;
	    if (anonymous == null && type.isInner() &&
		// First, get the parameter types
		!Modifier.isStatic(type.getModifiers())) {

		// Add on the extra parameter for inner non-static classes
		final Type[] origParams = parameters.getTypes();
		paramTypes = new Type[origParams.length + 1];
		paramTypes[0] = myType;
		System.arraycopy(origParams, 0, paramTypes, 1,
				 origParams.length);

		// Next, get the constructor
		theCons = type.getConstructor(paramTypes, myType);
		while (theCons == null && paramTypes[0].isInner()) {
		    paramTypes[0] = paramTypes[0].getDeclaringClass();
		    theCons = type.getConstructor(paramTypes, myType);
		}
	    } else {
		paramTypes = parameters.getTypes();
		theCons = type.getConstructor(paramTypes, myType);
	    }

	    /*
	    if (theCons == null) {
		System.err.println("**** Couldn't find constructor for " +
				   type + '(' + type.getClass() + ')');
		if (paramTypes.length > 0) {
		    System.err.print("Parameter types are ");
		    System.err.print(paramTypes[0].toString());
		    for (int i = 1; i < paramTypes.length; i++) {
			System.err.print(", ");
			System.err.print(paramTypes[i].toString());
		    }
		    System.err.println();
		}
		type.dump();
		System.err.println(symTable);
	    }
	    */

	    return type;	// It isn't an array, so return the type
	}

	// Yes, turn the base type into an array
	StringBuffer buf = new StringBuffer(type.getName());
	for (int i = 0; i < dimensions; i++)
	    buf.append("[]");
	try {
	    return topLevel.getType(buf.toString());
	} catch (ClassNotFoundException classEx) {
	    return null;
	}
    }

    protected Object computeValue() {
	return nonconstant;
    }

    protected Type[] computeExceptions() {
	if (dimensions != 0)
	    return noTypes;   // Creating arrays won't throw checked exceptions

	// The checked exceptions thrown are those thrown by evaluating the
	// parameters, plus those thrown by the constructor.  Finding the
	// constructor requires type evaluation.
	retrieveType();
	return Type.mergeTypeLists(parameters.getExceptionTypes(),
				   theCons.getExceptionTypes());
    }

    public VarList getVarList() {
	return (parameters == null) ? new VarList() : parameters.getVarList();
    }

    /**
     * Get the name of the type to instantiate
     *
     * @return the name of the type
     */
    public IdentifierAST getTypeName() {
	return typeName;
    }

    /**
     * Get the number of dimensions in the array to create
     *
     * @return the number of dimensions, or zero if this use of
     * <code>new</code> is creating an object
     */
    public int getDimensions() {
	return dimensions;
    }

    /**
     * Get the parameters to the object constructor
     *
     * @return a list containing the parameters to the constructor, or
     * <code>null</code> if this use of <code>new</code> is creating an array
     */
    public ListAST getParameters() {
	return parameters;
    }
}
