/*
 * @(#)$Id: ContinueAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.Type;
import jparse.VarList;
import jparse.expr.IdentifierAST;

/**
 * An AST node that represents a continue statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class ContinueAST extends StatementAST {

    /**
     * The continue label
     */
    private IdentifierAST label;

    /**
     * Create a new continue statement AST
     *
     * @param token the token represented by this AST node
     */
    public ContinueAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	final AST maybeLabel = getFirstChild();
	if (maybeLabel instanceof IdentifierAST) {
	    label = (IdentifierAST)maybeLabel;
	} else {
	    // There is no label, so the closest inclosing for, while, or
	    // do-while statement is the target of this continue
	    control = new StatementAST[] { context.continueTarget() };
	}
    }

    protected Type[] computeExceptions() {
	return noTypes;
    }

    protected StatementAST[] computeControl() {
	// This is only called if label is non-null
	return new StatementAST[] { symTable.getLabel(label.getName()) };
    }

    public VarList getVarList() {
	return new VarList();
    }

    /**
     * Get the label at which control should continue
     *
     * @return the label, or <code>null</code> if there is not one
     */
    public IdentifierAST getLabel() {
	return label;
    }
}
