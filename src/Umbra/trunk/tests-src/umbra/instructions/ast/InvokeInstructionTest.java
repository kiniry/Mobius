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

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author alx
 * @version a-01
 *
 */
public class InvokeInstructionTest {

  String[] lines = {
                    ""              
  };

  String[] mnemonics = {
                    ""              
  };

  InvokeInstruction[] instructions;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new InvokeInstruction[lines.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new InvokeInstruction(lines[i], mnemonics[i]);
    }
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#getInstruction()}.
   */
  @Test
  public void testGetInstruction() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#getMnemonics()}.
   */
  @Test
  public void testGetMnemonics() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#InvokeInstruction(java.lang.String, java.lang.String)}.
   */
  @Test
  public void testInvokeInstruction() {
    fail("Not yet implemented");
  }

}
