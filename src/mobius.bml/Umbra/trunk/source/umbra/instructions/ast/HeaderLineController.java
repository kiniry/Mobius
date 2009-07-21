/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import org.apache.bcel.generic.MethodGen;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

import annot.bcclass.BCMethod;

import umbra.editor.parsing.MethodRule;
import umbra.lib.BufferScanner;
import umbra.lib.BytecodeStrings;


/**
 * This is a class for lines in bytecode files that occur at the beginning
 * of methods. These are intended not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class HeaderLineController extends BytecodeLineController {

  /**
   * The identifier for the token.
   */
  private static final String HLC_TOKEN = "header line controller";

  /**
   * A BMLLib object that represents the method the header of which is
   * in the current object.
   */
  private BCMethod my_methodgen;

  /**
   * The recognition rule which parses method headers.
   */
  private MethodRule my_mrule;

  /**
   * This creates an instance of a bytecode line handle
   * which occurs at the beginning of a method
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public HeaderLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * Checks the correctness of the current header line. This method checks only
   * the approximate format. It uses the same heuristics as {@link MethodRule}
   * and also checks the prefixes in {@link BytecodeStrings#HEADER_PREFIX}.
   *
   * @return <code>true</code> when the line starts with a header prefix,
   *   <code>false</code> otherwise
   */
  public final boolean correct() {
    // class, package etc.
    for (int i = 0; i < BytecodeStrings.HEADER_PREFIX.length; i++) {
      if (getMy_line_text().contains(BytecodeStrings.HEADER_PREFIX[i])) {
        return true;
      }
    }

    // methods
    final MethodRule mrule = getMethodRule();
    final BufferScanner bs = new BufferScanner(getMy_line_text());
    final IToken tkn = mrule.evaluate(bs);
    return HLC_TOKEN.equals(tkn.getData());
  }

  /**
   * @return the rule to recognise the method headers
   */
  private MethodRule getMethodRule() {
    if (my_mrule == null) {
      my_mrule = new MethodRule(new Token(HLC_TOKEN));
    }
    return my_mrule;
  }

  /**
   * Returns the {@link BCMethod} structure responsible for the method in
   * which the instruction resides.
   *
   * @return the method in which the current instruction is located
   */
  public final BCMethod getMethod() {
    return my_methodgen;
  }

  /**
   * Sets the {@link BCMethod} structure responsible for the method the
   * header of which resides in the current object.
   *
   * @param a_mg the {@link BCMethod} structure to associate with the header
   */
  public final void setMethod(final BCMethod a_mg) {
    my_methodgen = a_mg;
  }
}
