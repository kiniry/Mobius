package mobius.logic.lang.generic.ast;

import mobius.logic.lang.generic.TypeChecker;

public class TypeCheckedAst {
  private final GenericAst ast;
  private final TypeChecker tc;
  
  public TypeCheckedAst(TypeChecker tc, GenericAst ast) {
    this.ast = ast;
    this.tc = tc;
  }

  public GenericAst getAst() {
    return ast;
  }

  public <R> R eval(Evaluator<R> t) {
    return ast.eval(t);
  }

  public TypeChecker getTypeChecker() {
    return tc;
  }
}
