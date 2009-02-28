package mobius.bmlvcgen.bml;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.Method.AccessFlag;

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
  
}
