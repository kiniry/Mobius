package jml2bml.bytecode;

import com.sun.source.tree.Tree;

public interface BytecodeUtils {
  /**
   * Inserts the given annotation into the bytecode
   * 
   * @param annotation
   */
  public void insertAnnotation(BmlAnnotation annotation);

  /**
   * Returns the corresponding location in the bytecode for given source code
   * node.
   */
  public Location findLocation(Tree node);

}
