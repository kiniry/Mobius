/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import static org.junit.Assert.*;

import org.apache.bcel.generic.Instruction;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import umbra.lib.BytecodeStrings;

/**
 * @author alx
 * @version a-01
 *
 */
public class PushInstructionTest {

  private PushInstruction[] instrs;
  
  private static String[] instrnames = {"bipush", "bipush",
                                        "sipush", "sipush" };

  private int[] inds = {6, -2, 3, -10};

  private static String[] lines = {
    "26:   bipush            6",
    "8:    bipush            -2",
    "8:    sipush            3",
    "8:    sipush            -10",};
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instrs = new PushInstruction[instrnames.length];
    for (int i = 0; i < instrnames.length; i++) {
      instrs[i] = new PushInstruction(lines[i], instrnames[i]);
    }
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ast.PushInstruction#getInstruction()}.
   */
  @Test
  public void testGetInstruction() {
    for (int i = 0; i < instrnames.length; i++) {   
      Instruction bcel = instrs[i].getInstruction();
      assertEquals(instrnames[i], bcel.getName());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.PushInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < instrnames.length; i++) {
      assertEquals("num=" + i, true, instrs[i].correct());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.PushInstruction#getMnemonics()}.
   */
  @Test
  public void testGetMnemonics() {
    final String [] strings = PushInstruction.getMnemonics();
    for (int i = 0; i < BytecodeStrings.PUSH_INS.length; i++) {
      assertEquals("index=" + i, BytecodeStrings.PUSH_INS[i], strings[i]);
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.PushInstruction#getInd()}.
   */
  @Test
  public void testGetInd() {
    for (int i = 0; i < instrnames.length; i++) {
      assertEquals("num=" + i, inds[i], instrs[i].getInd());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.PushInstruction#PushInstruction(java.lang.String, java.lang.String)}.
   */
  @Test
  public void testPushInstruction() {
    for (int i = 0; i < instrs.length; i++) {
      assertTrue(instrs[i].getName().equals(instrnames[i]));
    }
  }

}
