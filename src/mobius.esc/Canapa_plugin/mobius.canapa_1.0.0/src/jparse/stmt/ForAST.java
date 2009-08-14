/*
 * @(#)$Id: ForAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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

import antlr.CommonHiddenStreamToken;
import antlr.Token;
import antlr.collections.AST;
import jparse.HasExceptions;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;
import jparse.expr.ListAST;
import jparse.stmt.DeclarationAST;

/**
 * An AST node that represents a for statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class ForAST extends StatementAST implements JavaTokenTypes {

    /**
     * The initializer, either a
     * {@link jparse.stmt.DeclarationAST DeclarationAST} or a
     * {@link jparse.expr.ListAST ListAST}
     */
    private HasExceptions init;

    /**
     * The condition test
     */
    private jparse.expr.ExpressionAST cond;

    /**
     * The increment
     */
    private jparse.expr.ExpressionAST incr;

    /**
     * The statement
     */
    private StatementAST stmt;

    /**
     * Create a new for statement AST
     *
     * @param token the token represented by this AST node
     */
    public ForAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	final AST initNode = getFirstChild().getNextSibling();
	init = (HasExceptions)initNode.getFirstChild();
	final AST condNode = initNode.getNextSibling();
	final AST theCond = condNode.getFirstChild();
	cond = (theCond.getType() == SEMI)
	    ? null
	    : (jparse.expr.ExpressionAST)theCond;
	final AST incrNode = condNode.getNextSibling();
	incr = (jparse.expr.ExpressionAST)incrNode.getFirstChild();
	stmt = (StatementAST)incrNode.getNextSibling().getNextSibling();

	// Set up the break/continue context
	context.pushContinue(this);
	if (init != null && init instanceof ListAST) {
	    ((ListAST)init).parseComplete();
	} else {
	    ((DeclarationAST)init).parseComplete();
	}
	if (cond != null)
	    cond.parseComplete();
	if (incr != null)
	    incr.parseComplete();
	stmt.parseComplete();
	context.popContinue();
    }

    protected Type[] computeExceptions() {
	Type[] retVal = (cond == null)
	    ? init.getExceptionTypes()
	    : Type.mergeTypeLists(init.getExceptionTypes(),
				  cond.getExceptionTypes());
	retVal = Type.mergeTypeLists(retVal, incr.getExceptionTypes());
	return Type.mergeTypeLists(retVal, stmt.getExceptionTypes());
    }

    protected StatementAST[] computeControl() {
	return stmt.nextControlPoints();
    }

    public VarList getVarList() {
	final VarList initList = (init instanceof ListAST)
	    ? ((ListAST)init).getVarList()
	    : ((DeclarationAST)init).getVarList();
	return new VarList(new VarList(initList, cond.getVarList()),
			   new VarList(incr.getVarList(), stmt.getVarList()));
    }

    /**
     * Get the initialization clause of the for loop
     *
     * @return the initialization clause, which is either a
     * {@link jparse.stmt.DeclarationAST DeclarationAST} or a
     * {@link jparse.expr.ListAST ListAST}
     */
    public HasExceptions getInit() {
	return init;
    }

    /**
     * Get the condition clause of the for loop
     *
     * @return the condition clause
     */
    public jparse.expr.ExpressionAST getCondition() {
	return cond;
    }

    /**
     * Get the increment clause of the for loop
     *
     * @return the increment clause
     */
    public jparse.expr.ExpressionAST getIncrement() {
	return incr;
    }

    /**
     * Get the body of the for loop
     *
     * @return the body
     */
    public StatementAST getBody() {
	return stmt;
    }
        
	/* (non-Javadoc)
	 * @see antlr.CommonASTWithHiddenTokens#getHiddenAfter()
	 */
	public CommonHiddenStreamToken getHiddenAfter() {
		// TODO Auto-generated method stub
//		if (nastepny token to w¹s i nie ma komentarza pomiêdzy) {
//			zamien hidden na spacje;
//		}
		if (this.getNextSibling().getText().equals("{")) {
			boolean jest = false;
			CommonHiddenStreamToken t = getHiddenAfter();
			for (; t != null; t = t
			.getHiddenAfter()) {
				throw new RuntimeException("|" + t.getText() + "|");
/*				if (t.getText().startsWith("/*") || t.getText().startsWith("//")) {
					jest = true;
					break;
				}*/
			}
			if (!jest) {
				hiddenAfter.setText(" ");
			}
		}
		return super.getHiddenAfter();
	}
}
