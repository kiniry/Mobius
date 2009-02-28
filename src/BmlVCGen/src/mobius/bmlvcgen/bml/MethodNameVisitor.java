package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.ResultType;
import mobius.bmlvcgen.bml.types.Type;

/**
 * Visitor for method names and types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface MethodNameVisitor {
  /**
   * Visit method name.
   * @param name Name.
   */
  void visitName(String name);
  
  /**
   * Visit method return type.
   * @param t Return type.
   */
  void visitResultType(ResultType t);
  
  /**
   * Called before arguments are visited.
   */
  void beginArgs();
  
  /**
   * Visit method argument type.
   * @param t Argument type.
   * @param name Argument name (can be null).
   */
  void visitArg(Type t, String name);
  
  /**
   * Called after visiting arguments.
   */
  void endArgs();
}
