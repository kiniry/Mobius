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

import org.apache.bcel.classfile.ConstantUtf8;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class Utf8CPLineControllerTest extends TestCase {
  
  private String lines[] = {
    "   const    #5 =          Utf8 \"napis\"  ;",
    "const#5=Utf8 \"   inny napis  \";",
    "const #5 = Utf8 \"jeszcze inny napis  \";          ",
    "   const    #5 =  Utf8 \"  no i jeszcze jeden napis (53)\"   ;   "
  };
  
  private String strings[] = {
    "napis", "   inny napis  ", "jeszcze inny napis  ",
    "  no i jeszcze jeden napis (53)"                          
  };
  
  private String lines_incorrect[] = {
    "   const    5 =          Utf8 \"napis\";",
    "   const    #5 ==          Utf8 \"napis\";",
    "   const    5 =          Utf8 napis;",
    "   const    #5 ==          Utf8 'napis';",
    "   const    #5 =          cp1250 \"napis\";",
    "   const    #5 =          Utf8 \"kiepski napis;",
    "   const    #5 =          Utf8 inny napis\";",
    "   const    #5 =          Utf8 \"napis\"",
  };
  
  private Utf8CPLineController[] instructions;
  private Utf8CPLineController[] instructions_incorrect;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new Utf8CPLineController[lines.length];
    instructions_incorrect = new Utf8CPLineController[lines_incorrect.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new Utf8CPLineController(lines[i], null);
      instructions[i].correct();
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      instructions_incorrect[i] = new Utf8CPLineController(lines_incorrect[i], null);
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
   * Test method for {@link umbra.instructions.ast.Utf8CPLineController#getConstantNumber()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("utf8, constant number, ins number "
                 + i, instructions[i].getConstantNumber() == 5);
    }
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.Utf8CPLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("utf8, correct lines, ins number "
                 + i, instructions[i].correct());
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("utf8, incorrect lines, ins number "
                 + i, !instructions_incorrect[i].correct());
    }
  }
  
  /**
   * Test method for parameter parsing.
   */
  @Test
  public void testParams() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("utf8, params, ins number " + i,
                 ((ConstantUtf8) instructions[i].getConstant()).
                 getBytes().equals(strings[i]));
    }
  }

}
