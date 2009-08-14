/*
 * @(#)$Id: LabelAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a labeled statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class LabelAST extends StatementAST implements JavaTokenTypes {

    /**
     * The labeled statement
     */
    private StatementAST labeled;

    /**
     * Create a new labeled statement AST
     *
     * @param token the token represented by this AST node
     */
    public LabelAST(final Token token) {
	super(token);
	setType(LABELED_STAT);
    }

    public void parseComplete() {
	super.parseComplete();
	labeled = (StatementAST)getFirstChild().getNextSibling();
	labeled.parseComplete();
    }

    protected Type[] computeExceptions() {
	return labeled.getExceptionTypes();
    }

    protected StatementAST[] computeControl() {
	return labeled.nextControlPoints();
    }

    public VarList getVarList() {
	return labeled.getVarList();
    }

    /**
     * Get the statement that is labeled
     *
     * @return the statement with this label
     */
    public StatementAST getStatement() {
	return labeled;
    }
}
