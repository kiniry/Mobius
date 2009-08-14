/*
 * @(#)$Id: CaseGroupAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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

import antlr.collections.AST;
import java.util.ArrayList;
import java.util.HashSet;
import jparse.JavaAST;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a "case group"; i.e., a code block that starts
 * with one or more <code>case foo:</code> or <code>default:</code> labels
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class CaseGroupAST extends StatementAST implements JavaTokenTypes
{
    /**
     * The statement list
     */
    private StatementAST[] stmtList;

    /**
     * Create a new case group AST
     */
    public CaseGroupAST() {
	super();
	setType(CASE_GROUP);
    }

    /**
     * Set the statement list for this <code>CaseGroupAST</code>
     */
    public void parseComplete() {
	super.parseComplete();

	// Skip over the "case blah:" and "default:" labels at the start
	AST a = getFirstChild();
	while (a != null) {
	    final int t = a.getType();
	    if (t == LITERAL_case) {
		a = a.getNextSibling();
		((JavaAST)a).parseComplete();	// Parse the numbers
		a = a.getNextSibling().getNextSibling();
	    } else if (t == LITERAL_default) {
		a = a.getNextSibling().getNextSibling();
	    } else {
		break;
	    }
	}

	final ArrayList list = new ArrayList();
	while (a != null) {
	    list.add(a);
	    a = a.getNextSibling();
	}
	stmtList = new StatementAST[list.size()];
	list.toArray(stmtList);

	// Set the "next" pointers while completing the statements
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

    // See the equivalent method in CompoundStatement
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
     * Get the list of statements in this group
     *
     * @return the list of statements
     */
    public StatementAST[] getList() {
	return stmtList;
    }
}
