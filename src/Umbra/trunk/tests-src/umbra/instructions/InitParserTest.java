/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import annot.bcclass.BCClass;

import umbra.editor.BytecodeDocument;
import umbra.editor.BytecodeEditor;
import umbra.instructions.InitParser;
import umbra.instructions.LineContext;
import umbra.lib.BMLParsing;
import umbra.lib.UmbraLocationException;
import umbra.lib.UmbraMethodException;
import umbra.lib.UmbraSyntaxException;

/**
 * @author alx
 * @version a-01
 *
 */
public class InitParserTest {

  private static String my_content = 
    "package [default]\n" +
    "\n" +
    "Constant pool:\n" +
    "  const #1 = Class #2;\n" +
    "\n" +
    "public class List\n" +
    "\n" +
    "/*\n" +
    " *\n" +
    " */\n" +
    "public void <init>()\n" +
    "0:    aload_0\n" +
    "1:    invokespecial java.lang.Object.<init> ()V (10)\n" +
    "4:    return\n" +
    "\n" +
    "/*\n" +
    " *\n" +
    " */\n" +
    "public boolean replace(Object obj1, Object obj2)\n" +
    "0:    iconst_5\n" +
    "1:    istore_3\n" +
    "2:    goto    #27\n" +
    "5:    aload_0\n" +
    "6:    getfield    List.list [Ljava/lang/Object; (18)\n" +
    "9:    iload_3\n" +
    "10:   aaload\n" +
    "11:   aload_1\n" +
    "12:   if_acmpne   #24\n" +
    "15:   aload_0\n" +
    "16:   getfield    List.list [Ljava/lang/Object; (18)\n" +
    "19:   iload_3\n" +
    "20:   aload_2\n" +
    "21:   aastore\n" +
    "22:   iconst_1\n" +
    "23:   ireturn\n" +
    "24:   iinc    %3  1\n" +
    "27:   iload_3\n" +
    "28:   aload_0\n" +
    "29:   getfield    List.list [Ljava/lang/Object; (18)\n" +
    "32:   arraylength\n" +
    "33:   if_icmplt   #5\n" +
    "36:   iconst_0\n" +
    "37:   ireturn\n" +
    "";
  private BytecodeDocument my_doc;
  private InitParser my_parser;

  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    my_doc = new BytecodeDocument();
    my_doc.set(my_content);
    final ClassPath cp = 
     new ClassPath("tests-src/data");
    final SyntheticRepository repo = SyntheticRepository.getInstance(cp);
    final JavaClass jc = repo.loadClass("List");
    BytecodeEditor editor = new BytecodeEditor();
    my_doc.setEditor(editor, new BMLParsing(new BCClass(jc)));
    my_parser = new InitParser(my_doc, null, null);
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
    my_doc = null;
    my_parser = null;
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#InitParser(umbra.editor.BytecodeDocument, java.lang.String[])}.
   */
  @Test
  public void testInitParser() {
    InitParser a_parser = new InitParser(my_doc, null, null);
    assertTrue("wrong comments table", a_parser.getComments().isEmpty());
    assertTrue("wrong lines table", a_parser.getEditorLines().isEmpty());
    assertTrue("wrong instructions table",
               a_parser.getInstructions().isEmpty());
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#runParsing()}.
   */
  @Test
  public void testRunParsing() {
    try {
      my_parser.runParsing();
    } catch (UmbraLocationException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (UmbraMethodException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (UmbraSyntaxException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    assertTrue(my_parser.getEditorLines() != null);
    assertTrue(my_parser.getInstructions() != null);
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#removeCommentFromLine(java.lang.String)}.
   */
  @Test
  public void testRemoveCommentFromLine() {
    final LineContext ctxt = new LineContext();
    ctxt.setInitial();
    assertEquals("does not leave end of line", "something\n",
                 InitParser.removeCommentFromLine("something // something",
                                                  null));
    assertEquals("leaves whitespace", "something\n",
                   InitParser.removeCommentFromLine("something // ", null));    
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#extractCommentFromLine(java.lang.String, umbra.instructions.LineContext)}.
   */
  @Test
  public void testExtractCommentFromLine() {
    final LineContext ctxt = new LineContext();
    ctxt.setInitial();
    assertEquals("comment not extracted when no newline", " something",
               InitParser.extractCommentFromLine("something // something",
                                                 ctxt));
    assertEquals("comment not extracted with newline", " something",
                 InitParser.extractCommentFromLine("something // something\n\n",
                                                   ctxt));

  }

  /**
   * Test method for {@link umbra.instructions.InitParser#getEditorLines()}.
   */
  @Test
  public void testGetEditorLines() {
    //fail("Not yet implemented");
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#getInstructions()}.
   */
  @Test
  public void testGetInstructions() {
    //fail("Not yet implemented");
  }

  /**
   * Test method for {@link umbra.instructions.InitParser#getComments()}.
   */
  @Test
  public void testGetComments() {
    //fail("Not yet implemented");
  }

}
