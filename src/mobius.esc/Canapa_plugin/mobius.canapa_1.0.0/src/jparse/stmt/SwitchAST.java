/*
 * @(#)$Id: SwitchAST.java,v 1.3 2004/07/09 17:32:00 james Exp $
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
 * An AST node that represents a switch statement
 *
 * @version $Revision: 1.3 $, $Date: 2004/07/09 17:32:00 $
 * @author Jerry James
 */
public final class SwitchAST extends StatementAST implements JavaTokenTypes {

    /**
     * The expression to switch on
     */
    private jparse.expr.ExpressionAST expr;

    /**
     * The list of cases groups
     * Each cases group is a block of code separated by
     * <code>case</code> or <code>default</code> labels.
     */
    private CaseGroupAST[] groupList;

    /**
     * Create a new switch statement AST
     *
     * @param token the token represented by this AST node
     */
    public SwitchAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	expr = (jparse.expr.ExpressionAST)getFirstChild().getNextSibling();
	expr.parseComplete();

	// Construct an array of case groups
	final ArrayList list = new ArrayList();
	for (AST a = expr.getNextSibling().getNextSibling().getNextSibling();
	     a.getType() == CASE_GROUP; a = a.getNextSibling()) {
	    list.add(a);
	}
	groupList = new CaseGroupAST[list.size()];
	list.toArray(groupList);

	// Set the "next" pointers
	final StatementAST orig = context.nextStmt;
	context.pushBreak(this);
	for (int i = 0; i < groupList.length - 1; i++) {
	    context.nextStmt = groupList[i + 1];
	    groupList[i].parseComplete();
	}
	context.nextStmt = orig;
	if (groupList.length > 0)
	    {
		groupList[groupList.length - 1].parseComplete();
	    }
	context.popBreak();
    }

    protected Type[] computeExceptions() {
	Type[] retVal = expr.getExceptionTypes();
	for (int i = 0; i < groupList.length; i++) {
	    Type.mergeTypeLists(retVal, groupList[i].getExceptionTypes());
	}
	return retVal;
    }

    protected StatementAST[] computeControl() {
	// We use an iterative solution, much like with CompoundAST.  However,
	// we get to start over at each of the case groups.
	final HashSet goPoints = new HashSet();
	for (int i = 0; i < groupList.length; i++) {
	    final StatementAST[] next = groupList[i].nextControlPoints();
	    for (int j = 0; j < next.length; j++) {
		goPoints.add(next[j]);
	    }
	}

	// Now remove all of the statements inside the SwitchAST.
	for (int i = 0; i < groupList.length; i++) {
	    goPoints.remove(groupList[i]);
	}

	final StatementAST[] points = new StatementAST[goPoints.size()];
	return (StatementAST[])goPoints.toArray(points);
    }

    public VarList getVarList() {
	VarList list = expr.getVarList();
	for (int i = 0; i < groupList.length; i++) {
	    list = new VarList(list, groupList[i].getVarList());
	}
	return list;
    }

    /**
     * Get the expression that is switched on
     *
     * @return the expression for the switch
     */
    public jparse.expr.ExpressionAST getExpression() {
	return expr;
    }

    /**
     * Get the case groups within the switch statement
     *
     * @return an array containing the case groups
     */
    public CaseGroupAST[] getCaseGroups() {
	return groupList;
    }
}
