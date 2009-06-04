package ie.ucd.bon.ast;

import ie.ucd.bon.ast.TypeMark.Mark;

import java.util.Collections;
import java.util.List;

public final class Constants {

  public static final List<SpecificationElement> NO_SPEC_ELEMS = Collections.emptyList();
	public static final TypeMark NO_TYPE_MARK = TypeMark.mk(Mark.NONE, null, null);
	public static final List<Expression> NO_EXPRESSIONS = Collections.emptyList();
	public static final ContractClause EMPTY_CONTRACT = ContractClause.mk(NO_EXPRESSIONS, NO_EXPRESSIONS, null);
	public static final List<IndexClause> NO_INDEX_CLAUSES = Collections.emptyList();
	public static final List<ClassEntry> NO_CLASS_ENTRIES = Collections.emptyList();
}
