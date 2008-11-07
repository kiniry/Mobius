/*
 * @title "Umbra" @description "An editor for the Java bytecode and BML
 * specifications" @copyright "(c) 2006-2008 University of Warsaw" @license "All
 * rights reserved. This program and the accompanying materials are made
 * available under the terms of the LGPL licence see LICENCE.txt file"
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
public class InvokeInstructionTest {

  String[] lines = {
      "18:   invokevirtual  pl.tls.mobius.quiz.Question.getQuestion ()Ljava/lang/String; (48)",
      "7:    invokespecial  javax.microedition.lcdui.Form.<init> (Ljava/lang/String;)V (45)"
  };

  String[] wronglines = {
      "18:   invokevirtual  pl.tls.mobius.quiz.Question.getQuestion ()Ljava/lang/String (48)",
      "7:    invokesecial  javax.microedition.lcdui.Form.<init> (Ljava/lang/String;)V (45)"
  };

  String[] mnemonics = {
      "invokevirtual", "invokespecial"
  };

  String[] mnemonicnames = {
      "invokeinterface", "invokespecial", "invokestatic", "invokevirtual"
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
    for (int i = 0; i < lines.length; i++) {
      Instruction ins = instructions[i].getInstruction();
      String name = ins.getName();
      assertEquals("ins number " + i, name, mnemonics[i]);
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("ins number " + i, instructions[i].correct());
      InvokeInstruction iins = new InvokeInstruction(wronglines[i],
                                                     mnemonics[i]);
      assertFalse("ins number " + i, iins.correct());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#getMnemonics()}.
   */
  @Test
  public void testGetMnemonics() {
    String[] mm = InvokeInstruction.getMnemonics();
    for (int i = 0; i < mnemonicnames.length; i++) {
      assertEquals("mnemonic " + mnemonicnames[i], mm[i], mnemonicnames[i]);
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.InvokeInstruction#InvokeInstruction(java.lang.String, java.lang.String)}.
   */
  @Test
  public void testInvokeInstruction() {
    for (int i = 0; i < lines.length; i++) {
      InvokeInstruction ins = new InvokeInstruction(lines[i], mnemonics[i]);
      assertEquals("name " + i, ins.getName(), mnemonics[i]);
    }
  }

}
