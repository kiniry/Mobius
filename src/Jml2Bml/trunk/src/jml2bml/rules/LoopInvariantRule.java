/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-28 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;

import com.sun.tools.javac.util.Context;

import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0.0-1
 */
public class LoopInvariantRule extends TranslationRule<String, Symbols> {
  private final Context myContext;

  public LoopInvariantRule(final Context context) {
    super();
    this.myContext = context;
  }

  public String visitJmlStatementLoop(final JmlStatementLoop node, 
                                      final Symbols smbl) {
    throw new NotTranslatedException("Not implemented");
  }
}
