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

import org.apache.bcel.classfile.ConstantDouble;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class DoubleCPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Double 2.1  ;",
    "const#5=Double 2.1;",
    "const #5 = Double 2.1        ;  ",
    "   const    #5 =  Double 2.1;",
    "   const    #5 =          Double 2e+5  ;",
    "   const    #5 =          Double .23;    ",
    "   const    #5 =          Double 3.;",
    "   const    #5 =          Double +.34E-2  ;   ",
    "   const    #5 =          Double -0.324e4   ;",
    "   const    #5 =          Double 00.3424;",
    "   const    #5 =          Double -2.e3D;  ",
    "   const    #5 =          Double 4d;"
  };
  
  private double references[] = {
    2.1, 2.1, 2.1, 2.1, 200000.0, 0.23, 3.0, 0.0034, -3240.0, 0.3424, -2000.0, 4.0
  };
  
  private String lines_incorrect[] = {
    "   const    5 =          Double 2.1;",
    "   const    #5 ==          Double 2.1;",
    "   const    #5 =          dAbl 2.1;",
    "   const    #5 =          Double 2,1;",
    "   const    #5 =          Double 21;",
    "   const    #5 =          Double 2 .1;",
    "   const    #5 =          Double 2. 1;",
    "   const    #5 =          Double 2 . 1;",
    "   const    #5 =          Double 2e+;",
    "   const    #5 =          Double 34;",
    "   const    #5 =          Double 3.-3;",
    "   const    #5 =          Double 34E;",
    "   const    #5 =          Double -e4546;",
    "   const    #5 =          Double .d;",
    "   const    #5 =          Double 765.e-D;",
    "   const    #5 =          Double 2.4F;",
    "   const    #5 =          Double 2.4f;",
    "   const    #5 =          Double 2.4"
  };
  
  private DoubleCPLineController[] instructions;
  private DoubleCPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new DoubleCPLineController[lines.length];
    instructions_incorrect = new DoubleCPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new DoubleCPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new DoubleCPLineController(lines_incorrect[i], null);
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
   * Test method for {@link umbra.instructions.ast.DoubleCPLineController#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("double, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.DoubleCPLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("double, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("double, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("double, params, ins number " + i,
                 ((ConstantDouble) instructions[i].getConstant()).getBytes() ==
                   references[i]);
    }
  }

}
