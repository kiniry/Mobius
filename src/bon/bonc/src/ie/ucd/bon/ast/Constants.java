package ie.ucd.bon.ast;

import ie.ucd.bon.ast.TypeMark.Mark;

import java.util.ArrayList;
import java.util.List;

public final class Constants {

  public static final List<SpecificationElement> NO_SPEC_ELEMS = new ArrayList<SpecificationElement>(0);
	public static final TypeMark NO_TYPE_MARK = TypeMark.mk(Mark.NONE, null, null);
	public static final List<FeatureArgument> NO_ARGS = new ArrayList<FeatureArgument>(0);
	public static final List<Expression> NO_EXPRESSIONS = new ArrayList<Expression>(0);
	public static final ContractClause EMPTY_CONTRACT = ContractClause.mk(NO_EXPRESSIONS, NO_EXPRESSIONS, null);
	public static final List<ClusterEntry> NO_CLUSTER_ENTRIES = new ArrayList<ClusterEntry>(0);
	public static final List<IndexClause> NO_INDEX_CLAUSES = new ArrayList<IndexClause>(0);
	public static final List<DynamicComponent> NO_COMPONENTS = new ArrayList<DynamicComponent>(0);
}
