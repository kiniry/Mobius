/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-12 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.ast;

import java.io.PrintStream;

import com.sun.source.tree.Tree;

/**
 * JML pretty printer class.
 * @author kjk (kjk@mimuw.edu.pl)
 *
 * @version 0-0.1
 */
public class PrettyPrinter {
  /**
   * JMLTree pretty printer visitor(modified version of
   * com.sun.tools.javac.parser.TreePrinter).
   * @author kjk (kjk@mimuw.edu.pl)
   */
  private class PrettyPrinterVisitor extends
      ExtendedJmlTreeScanner < String, String > {

    /**
     * Method adds to default scan method printing the node class with
     * proper indentation.
     *
     * @param t tree node to scan
     * @param parentIndent indentation of parent node
     * @return returns parent indentation
     */
    @Override
    public String scan(final Tree t, final String parentIndent) {
      if (t == null)
        return parentIndent;
      out.println(parentIndent + t.getClass());
      super.scan(t, parentIndent + INDENT);
      return parentIndent;
    }
  }

  /** Indentation per level. */
  private static final String INDENT = "  ";

  /** The output stream. */
  private final PrintStream out;

  /** The pretty printer visitor. */
  private final PrettyPrinterVisitor printerVisitor;

  /**
   * Constructor of PrettyPrinter class.
   *
   * @param outStream stream used for printing.
   */
  public PrettyPrinter(final PrintStream outStream) {
    this.printerVisitor = new PrettyPrinterVisitor();
    this.out = outStream;
  }

  /**
   * Method used to print a tree.
   *
   * @param tree node to start printing with.
   */
  public void prettyPrint(final Tree tree) {
    printerVisitor.scan(tree, "");
  }
}
