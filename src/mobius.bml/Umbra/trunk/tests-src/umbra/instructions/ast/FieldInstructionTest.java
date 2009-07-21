/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import junit.framework.TestCase;

import org.apache.bcel.generic.Instruction;

import umbra.lib.BytecodeStrings;

/**
 * @author alx
 * @version a-01
 *
 */
public class FieldInstructionTest extends TestCase {

  
  private FieldInstruction instr;
  
  private static String instrname = "getfield";
  private static String line = 
    "16:   getfield   List.list [Ljava/lang/Object; (18)";


  /**
   * Sets up the test fixture. 
   * (Called before every test case method.) 
   */ 
  protected void setUp() { 
       instr = new FieldInstruction(line, instrname);
  } 


  /**
   * Tears down the test fixture. 
   * (Called after every test case method.) 
   */ 
  protected void tearDown() { 
       instr = null; 
  }

  /**
   * Test method for
   * {@link umbra.instructions.ast.FieldInstruction#getInstruction()}.
   */
  public void testGetInstruction() {
    Instruction bcel = instr.getInstruction();
    assertEquals(instrname, bcel.getName());
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
    final String [] strings = FieldInstruction.getMnemonics();
    for (int i = 0; i < BytecodeStrings.FIELD_INS.length; i++) {
      assertEquals(true, BytecodeStrings.FIELD_INS[i].equals(strings[i]));
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
