/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.tests;

import junit.framework.TestCase;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

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
  @Before
  public void setUp() throws Exception {
    instr = new LdcInstruction(line, instrname);
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
    instr = null;
  }
  /**
   * Test method for {@link umbra.instructions.ast.FieldInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    assertEquals(true, instr.correct());
  }

  /**
   * Test method for
   * {@link umbra.instructions.ast.FieldInstruction#getMnemonics()}.
   */
  @Test
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
  @Test
  public void testFieldInstruction() {
    instr.getName().equals(instrname);
  }

}
