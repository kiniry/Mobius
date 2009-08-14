/*
 * @(#)$Id: IfElseAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import java.util.HashSet;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents an if-else statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class IfElseAST extends StatementAST {

    /**
     * The conditional
     */
    private jparse.expr.ExpressionAST condition;

    /**
     * The "then" statement
     */
    private StatementAST thenStmt;

    /**
     * The "else" statement
     */
    private StatementAST elseStmt;

    /**
     * Create a new if-else statement AST
     *
     * @param token the token represented by this AST node
     */
    public IfElseAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	condition = (jparse.expr.ExpressionAST)getFirstChild()
	    .getNextSibling();
	condition.parseComplete();
	thenStmt = (StatementAST)condition.getNextSibling().getNextSibling();
	thenStmt.parseComplete();
	final AST elseLiteral = thenStmt.getNextSibling();
	if (elseLiteral != null) {
	    elseStmt = (StatementAST)elseLiteral.getNextSibling();
	    elseStmt.parseComplete();
	}
    }

    protected Type[] computeExceptions() {
	final Type[] body = (elseStmt == null)
	    ? thenStmt.getExceptionTypes()
	    : Type.mergeTypeLists(thenStmt.getExceptionTypes(),
				  elseStmt.getExceptionTypes());
	return Type.mergeTypeLists(condition.getExceptionTypes(), body);
    }

    protected StatementAST[] computeControl() {
	// Optimize for the common case
	if (elseStmt == null)
	    return thenStmt.nextControlPoints();

	final HashSet control = new HashSet();
	StatementAST[] points = thenStmt.nextControlPoints();
	for (int i = 0; i < points.length; i++) {
	    control.add(points[i]);
	}
	points = elseStmt.nextControlPoints();
	for (int i = 0; i < points.length; i++) {
	    control.add(points[i]);
	}

	points = new StatementAST[control.size()];
	return (StatementAST[])control.toArray(points);
    }

    public VarList getVarList() {
	return (elseStmt == null)
	    ? new VarList(condition.getVarList(), thenStmt.getVarList())
	    : new VarList(condition.getVarList(), thenStmt.getVarList(),
			  elseStmt.getVarList());
    }

    /**
     * Get the condition of the <code>if</code> statement
     *
     * @return the condition
     */
    public jparse.expr.ExpressionAST getCondition() {
	return condition;
    }

    /**
     * Get the <code>then</code> part of the <code>if</code> statement
     *
     * @return the then part
     */
    public StatementAST getThen() {
	return thenStmt;
    }

    /**
     * Get the <code>else</code> part of the <code>if</code> statement
     *
     * @return the else part
     */
    public StatementAST getElse() {
	return elseStmt;
    }
}
