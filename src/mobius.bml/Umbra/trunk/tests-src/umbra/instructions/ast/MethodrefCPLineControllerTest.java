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

import org.apache.bcel.classfile.ConstantMethodref;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class MethodrefCPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Methodref #21.#22  ;",
    "const#5=Methodref #21.#22;",
    "const #5 = Methodref #21.#22;          ",
    "   const    #5 =  Methodref       #21.#22  ; "
  };
  
  private int references[] = { 21, 21, 21, 21 };
  private int names[] = { 22, 22, 22, 22 };
  
  private String lines_incorrect[] = {
    "   const    5 =          Methodref #21.#22;",
    "   const    #5 ==          Methodref #21.#22;",
    "   const    #5 =          Methodreference #21.#22;",
    "   const    #5 =          Methodref 21.#22;",
    "   const    #5 =          Methodref #.#22;",
    "   const    #5 =          Methodref #21 .#22;",
    "   const    #5 =          Methodref #21. #22;",
    "   const    #5 =          Methodref #21 . #22;",
    "   const    #5 =          Methodref #21.#22",
  };
  
  private MethodrefCPLineController[] instructions;
  private MethodrefCPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new MethodrefCPLineController[lines.length];
    instructions_incorrect = new MethodrefCPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new MethodrefCPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new MethodrefCPLineController(lines_incorrect[i], null);
      instructions_incorrect[i].correct();
    }
  }
  
  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() {
    
  }

  /**
   * Test method for {@link umbra.instructions.ast.MethodrefCPLineController#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("methodref, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.MethodrefCPLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("methodref, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("methodref, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("methodref, params, ins number " + i,
                 ((ConstantMethodref) instructions[i].getConstant()).getClassIndex() ==
                   references[i] &&
                   ((ConstantMethodref) instructions[i].getConstant()).
                   getNameAndTypeIndex() == names[i]);
    }
  }

}
