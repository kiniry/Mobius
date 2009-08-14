/*
 * @(#)$Id: SynchronizedAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a synchronized block
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class SynchronizedAST extends StatementAST {

    /**
     * The object to lock
     */
    private jparse.expr.ExpressionAST lock;

    /**
     * The statement
     */
    private CompoundAST body;

    /**
     * Create a new synchronized statement AST
     *
     * @param token the token represented by this AST node
     */
    public SynchronizedAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	lock = (jparse.expr.ExpressionAST)getFirstChild().getNextSibling();
	body = (CompoundAST)lock.getNextSibling().getNextSibling();
	lock.parseComplete();
	body.parseComplete();
    }

    protected Type[] computeExceptions() {
	return Type.mergeTypeLists(lock.getExceptionTypes(),
				   body.getExceptionTypes());
    }

    protected StatementAST[] computeControl() {
	return body.nextControlPoints();
    }

    public VarList getVarList() {
	return new VarList(lock.getVarList(), body.getVarList());
    }

    /**
     * Get the object on which to acquire a lock
     *
     * @return the object to lock
     */
    public jparse.expr.ExpressionAST getLock() {
	return lock;
    }

    /**
     * Get the body of the <code>synchronized</code> statement
     *
     * @return the body
     */
    public StatementAST getBody() {
	return body;
    }
}
