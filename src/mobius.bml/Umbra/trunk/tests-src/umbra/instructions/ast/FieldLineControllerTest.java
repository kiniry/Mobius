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

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.FieldGen;
import org.apache.bcel.generic.Type;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import annot.bcclass.BCClass;

import umbra.lib.BMLParsing;

/**
 * @author alx
 * @version a-01
 *
 */
public class FieldLineControllerTest {


  String[] lines = {
      "private  int[] keyIds;",
  };

  FieldLineController[] instructions;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new FieldLineController[lines.length];
    ClassGen cg = new ClassGen("Test", "java.lang.Object", "",
                               Constants.ACC_PUBLIC,
                               null);
    FieldGen fg = new FieldGen(Constants.ACC_PUBLIC,
                               Type.getType("[I"), "keyIds",
                               cg.getConstantPool());
    cg.addField(fg.getField());
    JavaClass jc = cg.getJavaClass();
    BCClass bcc = new BCClass(jc);
    BMLParsing bmlp = new BMLParsing(bcc);
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new FieldLineController(lines[i], bmlp);
    }
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ast.FieldLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("line number " + i, instructions[i].correct());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.FieldLineController#isFieldLineStart(java.lang.String)}.
   */
  @Test
  public void testIsFieldLineStart() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("filed line start for number " + i,
                 FieldLineController.isFieldLineStart(instructions[i].
                                                        getLineContent()));
    }
  }

}
