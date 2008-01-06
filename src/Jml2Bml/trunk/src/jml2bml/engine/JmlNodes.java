package jml2bml.engine;

import org.jmlspecs.openjml.JmlTree;

import com.sun.tools.javac.tree.JCTree;

public class JmlNodes {
  /**
   * all nodes that represent some JML annotations; for this nodes translation
   * rules will be fired
   */
  public static final Class < ? > [] JML_CLASSES = {
                                                JmlTree.JmlStatementExpr.class,
                                                JCTree.JCAnnotation.class };

}
