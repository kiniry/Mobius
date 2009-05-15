package mobius.bmlvcgen.bml;

import mobius.bmlvcgen.bml.types.Type;

/**
 * Description of a local variable.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class LocalVariable {
  // Variable name.
  private final String name;
  // Variable index.
  private final int index;
  // Start of scope.
  private final int start;
  // End of scope.
  private final int end;
  // Variable type.
  private final Type type;
  
  /**
   * Visit a local variable.
   * @param name Variable name.
   * @param index Variable index.
   * @param start Start of variable scope.
   * @param end End of variable scope.
   * @param type Variable type.
   */
  public LocalVariable(final String name, 
                       final int index, 
                       final int start, 
                       final int end, 
                       final Type type) {
    this.name = name;
    this.index = index;
    this.start = start;
    this.end = end;
    this.type = type;
  }

  /**
   * Get variable name.
   * @return Variable name.
   */
  public String getName() {
    return name;
  }

  /**
   * Get variable index.
   * WARNING: Two or more variables can share
   * a single index (if their scopes are disjoint).
   * @return Variable index.
   */
  public int getIndex() {
    return index;
  }


  /**
   * Get scope start.
   * @return Scope start.
   */
  public int getStart() {
    return start;
  }


  /**
   * Get scope end.
   * @return Scope end.
   */
  public int getEnd() {
    return end;
  }

  /**
   * Get variable type.
   * @return Variable type.
   */
  public Type getType() {
    return type;
  }
  
  
}
