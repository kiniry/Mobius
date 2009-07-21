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
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.apache.bcel.classfile.ConstantClass;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ClassCPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Class #21 ; ",
    "const#5=Class #21;",
    "const #5 = Class #21          ;",
    "   const    #5 =  Class       #21;  "
  };
  
  private int references[] = { 21, 21, 21, 21, 21 };
  
  private String lines_incorrect[] = {
    "   const    5 =          Class #21;",
    "   const    #5 ==          Class #21;",
    "   const    #5 =          Klass #21;",
    "   const    #5 =          Class 21;",
    "   const    #5 =          Class #;",
    "   const    #5 =          Class #21"
  };
  
  private ClassCPLineController[] instructions;
  private ClassCPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new ClassCPLineController[lines.length];
    instructions_incorrect = new ClassCPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new ClassCPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new ClassCPLineController(lines_incorrect[i], null);
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
   * Test method for {@link umbra.instructions.ast.ClassCPInstruction#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("class, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.ClassCPInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("class, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("class, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("class, params, ins number " + i,
                 ((ConstantClass) instructions[i].getConstant()).getNameIndex() ==
                   references[i]);
    }
  }

}
