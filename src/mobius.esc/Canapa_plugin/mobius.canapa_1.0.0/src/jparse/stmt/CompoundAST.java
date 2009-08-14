/*
 * @(#)$Id: CompoundAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
 * An AST node that represents a compound statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class CompoundAST extends StatementAST implements JavaTokenTypes {

    /**
     * The statement list
     */
    private StatementAST[] stmtList;

    /**
     * Create a new compound statement AST
     *
     * @param token the token represented by this AST node
     */
    public CompoundAST(final Token token) {
	super(token);
	setType(SLIST);
    }

    /**
     * Set the statement list for this <code>CompoundAST</code>
     */
    public void parseComplete() {
	super.parseComplete();
	final ArrayList list = new ArrayList();
	for (AST a = getFirstChild(); a.getType() != RCURLY;
	     a = a.getNextSibling())
	    list.add(a);
	stmtList = new StatementAST[list.size()];
	list.toArray(stmtList);

	// Set the next pointers
	if (stmtList.length > 0) {
	    final StatementAST orig = context.nextStmt;
	    for (int i = 0; i < stmtList.length - 1; i++) {
		context.nextStmt = stmtList[i + 1];
		stmtList[i].parseComplete();
	    }
	    context.nextStmt = orig;
	    stmtList[stmtList.length - 1].parseComplete();
	}
    }

    protected Type[] computeExceptions() {
	Type[] exceptions = noTypes;
	for (int i = 0; i < stmtList.length; i++)
	    exceptions = Type.mergeTypeLists(exceptions,
					     stmtList[i].getExceptionTypes());
	return exceptions;
    }

    protected StatementAST[] computeControl() {
	if (stmtList.length == 0)
	    return new StatementAST[] { next };

	// We use an iterative solution.  We start by seeing where the first
	// statement can go.  If it can go to the next one, then ask it where
	// it can go, etc.  Continue until we run off the end or reach a place
	// where we can't go any further.
	final HashSet goPoints = new HashSet();
	goPoints.add(stmtList[0]);
	for (int i = 0; i < stmtList.length; i++) {
	    if (goPoints.contains(stmtList[i])) {
		final StatementAST[] sNext = stmtList[i].nextControlPoints();
		for (int j = 0; j < sNext.length; j++) {
		    goPoints.add(sNext[j]);
		}
	    }
	}

	// Now remove all of the statements inside the CompoundAST.  We have
	// to do this in a separate loop, since something may break to a label
	// earlier in the list, for example.
	for (int i = 0; i < stmtList.length; i++) {
	    goPoints.remove(stmtList[i]);
	}

	final StatementAST[] points = new StatementAST[goPoints.size()];
	return (StatementAST[])goPoints.toArray(points);
    }

    public VarList getVarList() {
	final VarList[] lists = new VarList[stmtList.length];
	for (int i = 0; i < lists.length; i++) {
	    lists[i] = stmtList[i].getVarList();
	}
	return new VarList(lists);
    }

    /**
     * Get the list of statements in this compound statement
     *
     * @return the list of statements
     */
    public StatementAST[] getList() {
	return stmtList;
    }
}
