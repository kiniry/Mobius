/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import junit.framework.TestCase;
import umbra.lib.BytecodeStrings;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class LdcInstructionTest extends TestCase {

  
  private LdcInstruction[] instr = new LdcInstruction[3];
  
  private static String instrname = "ldc";
  private static String[] line = {
    "0:   ldc    3.0 (16)",
    "4:   ldc    7.0 (17)",
    "3:    ldc               \"b a\" (25)"
  };

  /**
   * @throws java.lang.Exception
   */

  public void setUp() throws Exception {
    for (int i = 0; i < instr.length; i++) {
      instr[i] = new LdcInstruction(line[i], instrname);
    }
  }

  /**
   * @throws java.lang.Exception
   */

  public void tearDown() throws Exception {
    for (int i = 0; i < instr.length; i++) {
      instr[i] = null;
    }
  }
  /**
   * Test method for {@link umbra.instructions.ast.FieldInstruction#correct()}.
   */

  public void testCorrect() {
    for (int i = 0; i < instr.length; i++) {
      assertEquals(true, instr[i].correct());
    }
  }

  /**
   * Test method for
   * {@link umbra.instructions.ast.FieldInstruction#getMnemonics()}.
   */

  public void testGetMnemonics() {
    final String [] strings = LdcInstruction.getMnemonics();
    for (int i = 0; i < BytecodeStrings.LDC_INS.length; i++) {
      assertEquals(true, BytecodeStrings.LDC_INS[i].equals(strings[i]));
    }
  }

  /**
   * Test method for
   * {@link umbra.instructions.ast.FieldInstruction#
   *        FieldInstruction(java.lang.String, java.lang.String)}.
   */

  public void testFieldInstruction() {
    for (int i = 0; i < instr.length; i++) {
      assertTrue(instr[i].getName().equals(instrname));
    }
  }

}
