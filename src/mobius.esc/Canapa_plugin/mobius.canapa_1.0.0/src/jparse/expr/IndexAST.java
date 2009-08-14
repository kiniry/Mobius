/*
 * @(#)$Id: IndexAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
 * An AST node that represents an index expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class IndexAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The base of the index expression (i.e., the value being indexed)
     */
    private ExpressionAST base;

    /**
     * The index
     */
    private ExpressionAST index;

    /**
     * Create a new index expression AST
     *
     * @param token the token represented by this AST node
     */
    public IndexAST(final Token token) {
	super(token);
	setType(INDEX_OP);
    }

    public void parseComplete() {
	base = (ExpressionAST)getFirstChild();
	index = (ExpressionAST)base.getNextSibling();
	base.parseComplete();
	index.parseComplete();
    }

    protected Type computeType() {
	return base.retrieveType().getComponentType();
    }

    protected Type[] computeExceptions() {
	return Type.mergeTypeLists(base.getExceptionTypes(),
				   index.getExceptionTypes());
    }

    protected Object computeValue() {
	return nonconstant;
    }

    public VarList getVarList() {
	return new VarList(base.getVarList(), index.getVarList());
    }

    /**
     * Get the base of this index expression; i.e., the value being indexed
     *
     * @return the base of the expression
     */
    public ExpressionAST getBase() {
	return base;
    }

    /**
     * Get the index of this index expression
     *
     * @return the index of the expression
     */
    public ExpressionAST getIndex() {
	return index;
    }
}
