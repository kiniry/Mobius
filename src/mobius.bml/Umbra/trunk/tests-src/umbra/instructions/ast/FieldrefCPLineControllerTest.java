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

import org.apache.bcel.classfile.ConstantFieldref;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class FieldrefCPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Fieldref #21.#22;",
    "const#5=Fieldref #21.#22  ;",
    "const #5 = Fieldref #21.#22;          ",
    "   const    #5 =  Fieldref       #21.#22  ;  "
  };
  
  private int references[] = { 21, 21, 21, 21 };
  private int names[] = { 22, 22, 22, 22 };
  
  private String lines_incorrect[] = {
    "   const    5 =          Fieldref #21.#22;",
    "   const    #5 ==          Fieldref #21.#22;",
    "   const    #5 =          Fieldreference #21.#22;",
    "   const    #5 =          Fieldref 21.#22;",
    "   const    #5 =          Fieldref #.#22;",
    "   const    #5 =          Fieldref #21 .#22;",
    "   const    #5 =          Fieldref #21. #22;",
    "   const    #5 =          Fieldref #21 . #22;",
    "   const    #5 =          Fieldref #21.#22"
  };
  
  private FieldrefCPLineController[] instructions;
  private FieldrefCPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new FieldrefCPLineController[lines.length];
    instructions_incorrect = new FieldrefCPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new FieldrefCPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new FieldrefCPLineController(lines_incorrect[i], null);
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
   * Test method for {@link umbra.instructions.ast.FieldrefCPLineController#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("fieldref, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.FieldrefCPLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("fieldref, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("fieldref, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("fieldref, params, ins number " + i,
                 ((ConstantFieldref) instructions[i].getConstant()).getClassIndex() ==
                   references[i] &&
                   ((ConstantFieldref) instructions[i].getConstant()).
                   getNameAndTypeIndex() == names[i]);
    }
  }

}
