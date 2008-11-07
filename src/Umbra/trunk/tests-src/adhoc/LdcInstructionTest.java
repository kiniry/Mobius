/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package adhoc;

import junit.framework.TestCase;
import umbra.editor.parsing.BytecodeStrings;
import umbra.instructions.ast.LdcInstruction;

/**
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class LdcInstructionTest extends TestCase {

  
  private LdcInstruction instr;
  
  private static String instrname = "ldc";
  private static String line = 
    "3:    ldc               \"b a\" (25)";

  /**
   * @throws java.lang.Exception
   */

  public void setUp() throws Exception {
    instr = new LdcInstruction(line, instrname);
  }

  /**
   * @throws java.lang.Exception
   */

  public void tearDown() throws Exception {
    instr = null;
  }
  /**
   * Test method for {@link umbra.instructions.ast.FieldInstruction#correct()}.
   */

  public void testCorrect() {
    assertEquals(true, instr.correct());
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
    assertTrue(instr.getName().equals(instrname));
  }

}
