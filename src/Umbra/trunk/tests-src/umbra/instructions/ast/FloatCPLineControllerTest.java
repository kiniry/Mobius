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

import org.apache.bcel.classfile.ConstantFloat;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class FloatCPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Float 2.1  ;",
    "const#5=Float 2.1 ; ",
    "const #5 = Float 2.1;          ",
    "   const    #5 =  Float 2.1;",
    "   const    #5 =          Float 2e+5;",
    "   const    #5 =          Float .23;",
    "   const    #5 =          Float 3.;",
    "   const    #5 =          Float +.34E-2;",
    "   const    #5 =          Float -0.324e4;",
    "   const    #5 =          Float 00.3424;",
    "   const    #5 =          Float -2.e3f;",
    "   const    #5 =          Float 4F;"
  };
  
  private float references[] = {
    2.1f, 2.1f, 2.1f, 2.1f, 200000.0f, 0.23f,
    3.0f, 0.0034f, -3240.0f, 0.3424f, -2000.0f, 4.0f
  };
  
  private String lines_incorrect[] = {
    "   const    5 =          Float 2.1;",
    "   const    #5 ==          Float 2.1;",
    "   const    #5 =          flOUt 2.1;",
    "   const    #5 =          Float 2,1;",
    "   const    #5 =          Float 21;",
    "   const    #5 =          Float 2 .1;",
    "   const    #5 =          Float 2. 1;",
    "   const    #5 =          Float 2 . 1;",
    "   const    #5 =          Float 2e+;",
    "   const    #5 =          Float 34;",
    "   const    #5 =          Float 3.-3;",
    "   const    #5 =          Float 34E;",
    "   const    #5 =          Float -e4546;",
    "   const    #5 =          Float .f;",
    "   const    #5 =          Float 765.e-f;",
    "   const    #5 =          Float 2.4d;",
    "   const    #5 =          Float 2.4D;",
    "   const    #5 =          Float 2.1"
  };
  
  private FloatCPLineController[] instructions;
  private FloatCPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new FloatCPLineController[lines.length];
    instructions_incorrect = new FloatCPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new FloatCPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new FloatCPLineController(lines_incorrect[i], null);
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
   * Test method for {@link umbra.instructions.ast.FloatCPLineController#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("float, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.FloatCPLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("float, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("float, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("float, params, ins number " + i,
                 ((ConstantFloat) instructions[i].getConstant()).getBytes() ==
                   references[i]);
    }
  }

}
