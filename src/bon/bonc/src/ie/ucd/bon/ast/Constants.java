package ie.ucd.bon.ast;

import ie.ucd.bon.ast.TypeMark.Mark;

import java.util.ArrayList;
import java.util.List;

public final class Constants {

	public static final TypeMark NO_TYPE_MARK = TypeMark.mk(Mark.NONE, null);
	public static final List<FeatureArgument> NO_ARGS = new ArrayList<FeatureArgument>(0);
	public static final List<AssertionClause> NO_ASSERTIONS = new ArrayList<AssertionClause>(0);
	public static final ContractClause EMPTY_CONTRACT = ContractClause.mk(NO_ASSERTIONS, NO_ASSERTIONS);
	
}
