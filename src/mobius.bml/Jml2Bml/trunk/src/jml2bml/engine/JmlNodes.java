/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-28 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.engine;

import org.jmlspecs.openjml.JmlTree;

public class JmlNodes {
  /**
   * all nodes that represent some JML annotations; for this nodes translation
   * rules will be fired.
   */
  public static final Class < ? >[] JML_CLASSES = {
    JmlTree.JmlMethodDecl.class,
    JmlTree.JmlStatementLoop.class,
    JmlTree.JmlSpecificationCase.class,
    JmlTree.JmlStatementExpr.class,
    JmlTree.JmlTypeClauseExpr.class,
    JmlTree.JmlVariableDecl.class};
  
}
