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

/**
 * @author alx
 * @version a-01
 *
 */
public class IincInstructionTest {

  

  String[] lines = {
      "25:   iinc   %2  -1",
      "45:   iinc   %2  1"
  };

  String[] mnemonics = {
      "iinc",
      "iinc"
  };

  String[] mnemonicnames = {
      "iinc"
  };

  IincInstruction[] instructions;

  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new IincInstruction[lines.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new IincInstruction(lines[i], mnemonics[i]);
    }
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ast.IincInstruction#getInstruction()}.
   */
  @Test
  public void testGetInstruction() {
    for (int i = 0; i < lines.length; i++) {
      Instruction ins = instructions[i].getInstruction();
      String name = ins.getName();
      assertEquals("ins number " + i, name, mnemonics[i]);
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.IincInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("ins number " + i, instructions[i].correct());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.IincInstruction#getMnemonics()}.
   */
  @Test
  public void testGetMnemonics() {
    String[] mm = IincInstruction.getMnemonics();
    for (int i = 0; i < mnemonicnames.length; i++) {
      assertEquals("mnemonic " + mnemonicnames[i], mm[i], mnemonicnames[i]);
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.IincInstruction#IincInstruction(java.lang.String, java.lang.String)}.
   */
  @Test
  public void testIincInstruction() {
    for (int i = 0; i < lines.length; i++) {
      IincInstruction ins = new IincInstruction(lines[i], mnemonics[i]);
      assertEquals("name " + i, ins.getName(), mnemonics[i]);
    }
  }

}
