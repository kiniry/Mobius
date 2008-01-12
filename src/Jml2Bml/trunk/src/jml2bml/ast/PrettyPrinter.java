/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-12 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.ast;

import java.io.PrintStream;

import com.sun.source.tree.Tree;

/**
 * JML pretty printer class.
 * @author kjk (kjk@mimuw.edu.pl)
 */
public class PrettyPrinter {

  /**
   * JMLTree pretty printer visitor(modified version of 
   * com.sun.tools.javac.parser.TreePrinter).
   * @author kjk (kjk@mimuw.edu.pl)
   */
  private class PrettyPrinterVisitor extends
      ExtendedJmlTreeScanner<String, String> {
    public PrettyPrinterVisitor() {
      super();
    }

    public String scan(final Tree t, String p) {
      if (t == null)
        return p;
      out.println(p + t.getClass());
      super.scan(t, p + INDENT);
      return p;
    }
  }

  /** The output stream. */
  private final PrintStream out;

  /** The pretty printer visitor */
  private PrettyPrinterVisitor printerVisitor;

  /** Indentation per level */
  private static final String INDENT = "  ";

  public PrettyPrinter(final PrintStream out) {
    this.printerVisitor = new PrettyPrinterVisitor();
    this.out = out;
  }

  public void prettyPrint(final Tree tree) {
    tree.accept(printerVisitor, "");
  }
}
