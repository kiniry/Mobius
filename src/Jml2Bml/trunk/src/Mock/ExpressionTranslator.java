/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package Mock;

import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.BCExpression;
import annot.bcexpression.NumberLiteral;
import annot.io.Code;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.TreeScanner;
import com.sun.tools.javac.util.Context;

/**
 * Class responsible for translating JML expressions to BCExpression.
 * 
 * @author kjk
 * 
 */

public class ExpressionTranslator extends TreeScanner<BCExpression, Void> {
	private Context context;

	public BCExpression myScan(Tree node, Void p) {
		BCExpression result = scan(node, p);
		if (result == null)
			throw new RuntimeException("Not implemented node: "
					+ node.getKind() + ": " + node);
		return result;
	}

	public ExpressionTranslator(Context context) {
		this.context = context;
	}

	@Override
	public BCExpression visitLiteral(LiteralTree node, Void p) {
		Kind kind = node.getKind();
		if (kind == Kind.INT_LITERAL)
			return new NumberLiteral(((Integer) node.getValue()).intValue());
		throw new RuntimeException("Not implemented literal: " + node);
	};

	private int translateBinaryOperator(Kind kind) {
		//TODO: check if all translated ok
		if (kind == Kind.AND) return Code.AND;
//		if (kind == Kind.CONDITIONAL_AND) return
//		if (kind == Kind.CONDITIONAL_OR) return
		if (kind == Kind.DIVIDE) return Code.DIV;
		if (kind == Kind.EQUAL_TO) return Code.EQ;
		if (kind == Kind.GREATER_THAN) return Code.GRT;
		if (kind == Kind.GREATER_THAN_EQUAL) return Code.GRTEQ;
		if (kind == Kind.LEFT_SHIFT) return Code.SHL;
		if (kind == Kind.LESS_THAN) return Code.LESS;
		if (kind == Kind.LESS_THAN_EQUAL) return Code.LESSEQ;
		if (kind == Kind.MINUS) return Code.MINUS;
		if (kind == Kind.MULTIPLY) return Code.MULT;
		if (kind == Kind.NOT_EQUAL_TO) return Code.NOTEQ;
		if (kind == Kind.OR) return Code.OR;
		if (kind == Kind.PLUS) return Code.PLUS;
		if (kind == Kind.REMAINDER) return Code.REM;
		if (kind == Kind.RIGHT_SHIFT) return Code.SHR;
//		if (kind == Kind.UNSIGNED_RIGHT_SHIFT) return
//		if (kind == Kind.XOR) return 
		throw new RuntimeException("Not implemented binary operator: " + kind);
	}

	@Override
	public BCExpression visitBinary(BinaryTree node, Void p) {
		BCExpression leftExpression = myScan(node.getLeftOperand(), p);
		BCExpression righrExpression = myScan(node.getRightOperand(), p);
		int operator = translateBinaryOperator(node.getKind());
		return new ArithmeticExpression(operator, leftExpression,
				righrExpression);
	}

	@Override
	public BCExpression visitIdentifier(IdentifierTree node, Void p) {
		System.out.println("visitIdentifier ");
		// TODO: find out what is the identifier
		return null;
	}
}
