/*
 * @(#)$Id: TryAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
package jparse.stmt;

import antlr.Token;
import antlr.collections.AST;
import java.util.ArrayList;
import java.util.HashSet;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a try-catch-finally statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class TryAST extends StatementAST implements JavaTokenTypes {

    /**
     * The try block
     */
    private CompoundAST block;

    /**
     * The catch clauses
     */
    private CatchAST[] catchClause;

    /**
     * The finally clause
     */
    private CompoundAST finallyClause;

    /**
     * Create a new try-catch-finally statement AST
     *
     * @param token the token represented by this AST node
     */
    public TryAST(final Token token) {
	super(token);
    }

    /**
     * Set the instance variables
     */
    public void parseComplete() {
	super.parseComplete();

	// The "try" block
	block = (CompoundAST)getFirstChild();
	block.parseComplete();

	// The "catch" clauses
	final ArrayList list = new ArrayList();
	AST a;
	for (a = block.getNextSibling(); a != null && a instanceof CatchAST;
	     a = a.getNextSibling()) {
	    list.add(a);
	}
	catchClause = new CatchAST[list.size()];
	list.toArray(catchClause);
	for (int i = 0; i < catchClause.length; i++) {
	    catchClause[i].parseComplete();
	}

	// The "finally" clause
	if (a != null && a.getType() == LITERAL_finally) {
	    finallyClause = (CompoundAST)a.getNextSibling();
	    finallyClause.parseComplete();
	}
    }

    protected Type[] computeExceptions() {
	// Compute the exceptions thrown by the try block
	Type[] exceptions = block.getExceptionTypes();

	// Now, for each catch clause, subtract off the exception it catches
	// and add on the ones that its body throws
	for (int i = 0; i < catchClause.length; i++) {
	    exceptions = catchClause[i].removeCaughtException(exceptions);
	    exceptions =
		Type.mergeTypeLists(exceptions,
				    catchClause[i].getExceptionTypes());
	}

	// Then add on any exceptions thrown by the finally clause
	if (finallyClause != null) {
	    exceptions =
	    Type.mergeTypeLists(exceptions, finallyClause.getExceptionTypes());
	}

	return exceptions;
    }

    protected StatementAST[] computeControl() {
	final HashSet goPoints = new HashSet();
	StatementAST[] sPoints = block.nextControlPoints();
	for (int i = 0; i < sPoints.length; i++) {
	    goPoints.add(sPoints[i]);
	}

	for (int i = 0; i < catchClause.length; i++) {
	    sPoints = catchClause[i].nextControlPoints();
	    for (int j = 0; j < sPoints.length; j++) {
		goPoints.add(sPoints[j]);
	    }
	}
	
	if (finallyClause != null) {
	    sPoints = finallyClause.nextControlPoints();
	    for (int i = 0; i < sPoints.length; i++) {
		goPoints.add(sPoints[i]);
	    }
	}

	final StatementAST[] points = new StatementAST[goPoints.size()];
	return (StatementAST[])goPoints.toArray(points);
    }

    public VarList getVarList() {
	VarList list = block.getVarList();
	if (catchClause.length > 0) {
	    VarList[] lists = new VarList[catchClause.length];
	    for (int i = 0; i < catchClause.length; i++) {
		lists[i] = catchClause[i].getVarList();
	    }
	    list = new VarList(list, new VarList(lists));
	}
	return (finallyClause == null)
	    ? list
	    : new VarList(list, finallyClause.getVarList());
    }

    /**
     * Get the <code>try</code> block
     *
     * @return the <code>try</code> block
     */
    public CompoundAST getTryBlock() {
	return block;
    }

    /**
     * Get the list of catch clauses for this <code>try</code>
     *
     * @return an array containing the catch clauses
     */
    public CatchAST[] getCatchClauses() {
	return catchClause;
    }

    /**
     * Get the <code>finally</code> clause for this <code>try</code>, if any
     *
     * @return the <code>finally</code> clause, or <code>null</code> if there
     * is not one
     */
    public CompoundAST getFinallyClause() {
	return finallyClause;
    }
}
