package mobius.bmlvcgen.bml;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.Method.AccessFlag;
import mobius.bmlvcgen.util.Visitable;

/**
 * Interface of objects used to visit method declarations.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface MethodVisitor {
  /**
   * Visit access flags.
   * @param flags Access flags.
   */
  void visitFlags(EnumSet<AccessFlag> flags);
  
  /**
   * Visit method name and type.
   * @param name Method name and type.
   */
  void visitName(MethodName name);
  
  /**
   * Called before visiting local variables.
   * @param maxLocals Max variable index.
   */
  void beginLocals(int maxLocals);
  
  /**
   * Visit a local variable.
   * @param var Variable description.
   */
  void visitLocal(LocalVariable var);
  
  /**
   * Called after visiting local variables.
   */
  void endLocals();
  
  
  
  /**
   * Called before visiting specification cases.
   */
  void beginSpecs();

  /**
   * Visit a specification case.
   * @param spec Specification case.
   */
  void visitSpecification(MethodSpec spec);
  
  /**
   * Called after visiting specification cases.
   */
  void endSpecs();
  
  /**
   * Called before visiting assertions.
   */
  void beginAssertions();
  
  /**
   * Visit an assertion.
   * @param i Instruction index.
   * @param type Assertion type (pre or post).
   * @param expr Assertion formula.
   */
  void visitAssertion(int i, 
                      AssertType type,
                      Visitable<? super AssertExprVisitor> expr);
  
  /**
   * Called after visiting assertions.
   */
  void endAssertions();
    
  // TODO: Loop invariants.
}
