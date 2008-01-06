package jml2bml.engine;

import com.sun.source.tree.Tree;

public class JmlTokens {
	public final static String NON_NULL = "org.jmlspecs.annotations.NonNull";
	public final static String ASSERT = "assert";
	
	public static String operatorName(Tree.Kind kind) {
		if (kind.equals(Tree.Kind.UNARY_PLUS))
			return "+";
		if (kind.equals(Tree.Kind.UNARY_MINUS))
			return "-";
		if (kind.equals(Tree.Kind.LOGICAL_COMPLEMENT))
			return "!";
		if (kind.equals(Tree.Kind.BITWISE_COMPLEMENT))
			return "~";
		if (kind.equals(Tree.Kind.PREFIX_INCREMENT))
			return "++";
		if (kind.equals(Tree.Kind.PREFIX_DECREMENT))
			return "--";
		if (kind.equals(Tree.Kind.POSTFIX_INCREMENT))
			return "++";
		if (kind.equals(Tree.Kind.POSTFIX_DECREMENT))
			return "--";
		if (kind.equals(Tree.Kind.OTHER))
			return "<*nullchk*>";
		if (kind.equals(Tree.Kind.CONDITIONAL_OR))
			return "||";
		if (kind.equals(Tree.Kind.CONDITIONAL_AND))
			return "&&";
		if (kind.equals(Tree.Kind.EQUAL_TO))
			return "==";
		if (kind.equals(Tree.Kind.NOT_EQUAL_TO))
			return "!=";
		if (kind.equals(Tree.Kind.LESS_THAN))
			return "<";
		if (kind.equals(Tree.Kind.GREATER_THAN))
			return ">";
		if (kind.equals(Tree.Kind.LESS_THAN_EQUAL))
			return "<=";
		if (kind.equals(Tree.Kind.GREATER_THAN_EQUAL))
			return ">=";
		if (kind.equals(Tree.Kind.OR))
			return "|";
		if (kind.equals(Tree.Kind.XOR))
			return "^";
		if (kind.equals(Tree.Kind.AND))
			return "&";
		if (kind.equals(Tree.Kind.LEFT_SHIFT))
			return "<<";
		if (kind.equals(Tree.Kind.RIGHT_SHIFT))
			return ">>";
		if (kind.equals(Tree.Kind.UNSIGNED_RIGHT_SHIFT))
			return ">>>";
		if (kind.equals(Tree.Kind.PLUS))
			return "+";
		if (kind.equals(Tree.Kind.MINUS))
			return "-";
		if (kind.equals(Tree.Kind.MULTIPLY))
			return "*";
		if (kind.equals(Tree.Kind.DIVIDE))
			return "/";
		if (kind.equals(Tree.Kind.REMAINDER))
			return "%";
		throw new Error();

	}
}
