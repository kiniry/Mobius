/**
 * 
 */
package annot.textio;

import static org.junit.Assert.*;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import annot.textio.BMLParser.quantifiedFormula_return;

/**
 * @author alx
 *
 */
public class BMLParserTest {

  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link annot.textio.BMLParser#BMLParser(org.antlr.runtime.TokenStream)}.
   */
  @Test
  public void testBMLParser() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#setTreeAdaptor(org.antlr.runtime.tree.TreeAdaptor)}.
   */
  @Test
  public void testSetTreeAdaptor() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#getTreeAdaptor()}.
   */
  @Test
  public void testGetTreeAdaptor() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#getTokenNames()}.
   */
  @Test
  public void testGetTokenNames() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#getGrammarFileName()}.
   */
  @Test
  public void testGetGrammarFileName() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#initClass(annot.bcclass.BCClass, boolean)}.
   */
  @Test
  public void testInitClass() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#init(annot.bcclass.BCClass, annot.bcclass.BCMethod, annot.bcclass.BCConstantPool, org.apache.bcel.generic.InstructionHandle, int)}.
   */
  @Test
  public void testInit() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#reportError(org.antlr.runtime.RecognitionException)}.
   */
  @Test
  public void testReportErrorRecognitionException() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#getBMLPositions()}.
   */
  @Test
  public void testGetBMLPositions() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#parseClass()}.
   */
  @Test
  public void testParseClass() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#fileheader()}.
   */
  @Test
  public void testFileheader() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#packageinfo()}.
   */
  @Test
  public void testPackageinfo() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#typename()}.
   */
  @Test
  public void testTypename() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#constant_pools()}.
   */
  @Test
  public void testConstant_pools() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#constant_pool()}.
   */
  @Test
  public void testConstant_pool() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#second_constant_pool()}.
   */
  @Test
  public void testSecond_constant_pool() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#constant_pool_content()}.
   */
  @Test
  public void testConstant_pool_content() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#constant_pool_line()}.
   */
  @Test
  public void testConstant_pool_line() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#constant_pool_entry()}.
   */
  @Test
  public void testConstant_pool_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#class_cp_entry()}.
   */
  @Test
  public void testClass_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#field_cp_entry()}.
   */
  @Test
  public void testField_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#method_cp_entry()}.
   */
  @Test
  public void testMethod_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#interface_method_cp_entry()}.
   */
  @Test
  public void testInterface_method_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#string_cp_entry()}.
   */
  @Test
  public void testString_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#integer_cp_entry()}.
   */
  @Test
  public void testInteger_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#float_cp_entry()}.
   */
  @Test
  public void testFloat_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#long_cp_entry()}.
   */
  @Test
  public void testLong_cp_entry() {
    String[] paramdecls = { "Long 1000L;",
                            "Long 0L;",
                            "Long -10L;"
                            };
    String[] answers = { "Long 1000L ;",
                         "Long 0L ;",
                         "Long - 10L ;"
                         };
    System.out.println("testLong_cp_entry: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.long_cp_entry_return ret;
      try {
        ret = parser.long_cp_entry();
        assertEquals("long_cp_entry: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testLong_cp_entry end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#double_cp_entry()}.
   */
  @Test
  public void testDouble_cp_entry() {
    String[] paramdecls = { "Double 1000.0D;",
                            "Double 0.0D;",
                            "Double -10.0d;"
                            };
    String[] answers = { "Double 1000 . 0 D ;",
                         "Double 0 . 0 D ;",
                         "Double - 10 . 0 d ;"
                         };
    System.out.println("testDouble_cp_entry: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.double_cp_entry_return ret;
      try {
        ret = parser.double_cp_entry();
        assertEquals("double_cp_entry: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testDouble_cp_entry end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#name_and_type_cp_entry()}.
   */
  @Test
  public void testName_and_type_cp_entry() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#utf8_cp_entry()}.
   */
  @Test
  public void testUtf8_cp_entry() {
    String[] paramdecls = { "Utf8 \"ala\";",
                            "Utf8 \"\";",
                            "Utf8 \"I have just completed the test! My score was: \";"
                            };
    String[] answers = { "Utf8 \"ala\" ;",
                         "Utf8 \"\" ;",
                         "Utf8 \"I have just completed the test! My score was: \" ;"
                         };
    System.out.println("testUtf8_cp_entry: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.utf8_cp_entry_return ret;
      try {
        ret = parser.utf8_cp_entry();
        assertEquals("utf8_cp_entry: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testUtf8_cp_entry end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#cp_ref()}.
   */
  @Test
  public void testCp_ref() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#sign()}.
   */
  @Test
  public void testSign() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#exponent_indicator()}.
   */
  @Test
  public void testExponent_indicator() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#signed_integer()}.
   */
  @Test
  public void testSigned_integer() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#exponent_part()}.
   */
  @Test
  public void testExponent_part() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#floating_point_literal()}.
   */
  @Test
  public void testFloating_point_literal() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#float_type_suffix()}.
   */
  @Test
  public void testFloat_type_suffix() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#typeheader()}.
   */
  @Test
  public void testTypeheader() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#dotedname()}.
   */
  @Test
  public void testDotedname() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#classmodifiers()}.
   */
  @Test
  public void testClassmodifiers() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#interfacemodifiers()}.
   */
  @Test
  public void testInterfacemodifiers() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#classmodifier()}.
   */
  @Test
  public void testClassmodifier() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#interfacemodifier()}.
   */
  @Test
  public void testInterfacemodifier() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#class_extends_clause()}.
   */
  @Test
  public void testClass_extends_clause() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#interface_extends_clause()}.
   */
  @Test
  public void testInterface_extends_clause() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#implements_clause()}.
   */
  @Test
  public void testImplements_clause() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#name_list()}.
   */
  @Test
  public void testName_list() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#typebody()}.
   */
  @Test
  public void testTypebody() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticsection()}.
   */
  @Test
  public void testStaticsection() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticfields()}.
   */
  @Test
  public void testStaticfields() {
    String[] paramdecls = { "static private int sum;\n",
                            "static private int sum;\n"+
                            "static private int sum1;\n"
                            };
    String[] answers = { "static private int sum ; \n",
                         "static private int sum ; \n "+
                         "static private int sum1 ; \n"
                         };
    System.out.println("testStaticfields: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.staticfields_return ret;
      try {
        ret = parser.staticfields();
        String res =  ret.tree.toStringTree();
        assertEquals("staticfields: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testStaticfields end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#field()}.
   */
  @Test
  public void testStaticfield() {
    String[] paramdecls = { "static private int sum;",
                            "static public java.lang.Object a;"
                            };
    String[] answers = { "static private int sum ;",
                         "static public java . lang . Object a ;"
                         };
    System.out.println("testStaticfield: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.staticfield_return ret;
      try {
        ret = parser.staticfield();
        assertEquals("field: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testStaticfield end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#field()}.
   */
  @Test
  public void testField() {
    String[] paramdecls = { "private int sum;",
                            "private int[] sum;",
                            "private  int[] keyIds;",
                            "public java.lang.Object a;"
                            };
    String[] answers = { "private int sum ;",
                         "private int [ ] sum ;",
                         "private int [ ] keyIds ;",
                         "public java . lang . Object a ;"
                         };
    System.out.println("testField: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.field_return ret;
      try {
        ret = parser.field();
        assertEquals("field: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testField end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticspec()}.
   */
  @Test
  public void testStaticspec() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticinvariants()}.
   */
  @Test
  public void testStaticinvariants() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticconstraints()}.
   */
  @Test
  public void testStaticconstraints() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticrepresents()}.
   */
  @Test
  public void testStaticrepresents() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#staticinitially()}.
   */
  @Test
  public void testStaticinitially() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectsection()}.
   */
  @Test
  public void testObjectsection() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectfields()}.
   */
  @Test
  public void testObjectfields() {
    String[] paramdecls = { "private int sum;\n",
                            "private int sum;\n"+
                            "private int sum1;\n"
                            };
    String[] answers = { "private int sum ; \n",
                         "private int sum ; \n "+
                         "private int sum1 ; \n"
                         };
    System.out.println("testObjectfields: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.objectfields_return ret;
      try {
        ret = parser.objectfields();
        String res =  ret.tree.toStringTree();
        assertEquals("objectfields: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testObjectfields end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectspec()}.
   */
  @Test
  public void testObjectspec() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectinvariants()}.
   */
  @Test
  public void testObjectinvariants() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectinvariant()}.
   */
  @Test
  public void testObjectinvariant() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectconstraints()}.
   */
  @Test
  public void testObjectconstraints() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectrepresents()}.
   */
  @Test
  public void testObjectrepresents() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#objectinitially()}.
   */
  @Test
  public void testObjectinitially() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#method()}.
   */
  @Test
  public void testMethod() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#method_body()}.
   */
  @Test
  public void testMethod_body() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#methodmodifiers()}.
   */
  @Test
  public void testMethodmodifiers() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#methodmodifier()}.
   */
  @Test
  public void testMethodmodifier() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#type_spec()}.
   */
  @Test
  public void testType_spec() {
    String[] paramdecls = { "int",
                            "java.lang.Object",
                            "java.lang.Object[]",
                            "int[]"
                            };
    String[] answers = { "int",
                         "java . lang . Object",
                         "java . lang . Object [ ]",
                         "int [ ]"
                         };
    System.out.println("testArr_type: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.type_spec_return ret;
      try {
        ret = parser.type_spec();
        String res =  ret.tree.toStringTree();
        assertEquals("type_spec: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testArr_type end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#type()}.
   */
  @Test
  public void testType() {
    String[] paramdecls = { "int",
                            "java.lang.Object",
                            "float",
                            "boolean"
                            };
    String[] answers = { "int",
                         "java . lang . Object",
                         "float",
                         "boolean"
                         };
    System.out.println("testType: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.type_return ret;
      try {
        ret = parser.type();
        String res =  ret.tree.toStringTree();
        assertEquals("arr_type: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testType end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#reference_type()}.
   */
  @Test
  public void testReference_type() {
    String[] paramdecls = { "java.lang.Object"
                            };
    String[] answers = { "java . lang . Object"
                         };
    System.out.println("testReference_type: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.reference_type_return ret;
      try {
        ret = parser.reference_type();
        String res =  ret.tree.toStringTree();
        assertEquals("Reference_type: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testReference_type end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#built_in_type()}.
   */
  @Test
  public void testBuilt_in_type() {
    String[] paramdecls = {  "void",
                             "boolean",
                             "byte",
                             "char",
                             "short",
                             "int",
                             "long",
                             "float",
                             "double"
    };
    String[] answers = { "void",
                         "boolean",
                         "byte",
                         "char",
                         "short",
                         "int",
                         "long",
                         "float",
                         "double"
    };
    System.out.println("testBuilt_in_type: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.built_in_type_return ret;
      try {
        ret = parser.built_in_type();
        String res =  ret.tree.toStringTree();
        assertEquals("Built_in_type: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testBuilt_in_type end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#methodheader()}.
   */
  @Test
  public void testMethodheader() {
    String[] paramdecls = { "<init>()\n",
                            "<clinit>()\n",
                            "ala()\n",
                            "ala(int)\n",
                            "ala(String x, int d)\n",
                            "ala$1(String x, int d)\n"
    };
    String[] answers = {
                        "<init> ( ) \n",
                        "<clinit> ( ) \n",
                        "ala ( ) \n",
                        "ala ( int ) \n",
                        "ala ( String x , int d ) \n",
                        "ala $ 1 ( String x , int d ) \n",
    };
    System.out.println("testMethodheader: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.methodheader_return ret;
      try {
        ret = parser.methodheader();
        assertEquals("method header: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testMethodheader end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#formals()}.
   */
  @Test
  public void testFormals() {
    String[] paramdecls = { "()",
                            "(String)",
                            "(int)",
                            "(Strint x, int d)",
                            "(int d , int c)"
    };
    String[] answers = {"( )",
                        "( String )",
                        "( int )",
                        "( Strint x , int d )",
                        "( int d , int c )"
    };
    System.out.println("testFormals: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.formals_return ret;
      try {
        ret = parser.formals();
        assertEquals("formals: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testFormals end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#param_declaration_list()}.
   */
  @Test
  public void testParam_declaration_list() {
    String[] paramdecls = { "java.lang.Character n, String x",
    "javax.microedition.lcdui.Command c, javax.microedition.lcdui.Displayable d",
    "javax.microedition.lcdui.Command c, javax.microedition.lcdui.Displayable e"
    };
    String[] answers = {
       "java . lang . Character n , String x", 
       "javax . microedition . lcdui . Command c , javax . microedition . lcdui . Displayable d",
       "javax . microedition . lcdui . Command c , javax . microedition . lcdui . Displayable e" };
    System.out.println("testParam_declaration_list: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.param_declaration_list_return ret;
      try {
        ret = parser.param_declaration_list();
        assertEquals("param declaration list: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testParam_declaration_list end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#param_declaration()}.
   */
  @Test
  public void testParam_declaration() {
    String[] paramdecls = { "java.lang.Character n", "String x" };
    String[] answers = { "java . lang . Character n", "String x" };
    System.out.println("testParam_declaration: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      BMLParser.param_declaration_return ret;
      try {
        ret = parser.param_declaration();
        assertEquals("param declaration: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testParam_declaration end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#param_declaration_noname()}.
   */
  @Test
  public void testParam_declaration_noname() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#param_modifier()}.
   */
  @Test
  public void testParam_modifier() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#dims()}.
   */
  @Test
  public void testDims() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#throws_clause()}.
   */
  @Test
  public void testThrows_clause() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#bml_in_method_spec()}.
   */
  @Test
  public void testBml_in_method_spec() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#instruction_line()}.
   */
  @Test
  public void testInstruction_line() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#printableAttribute()}.
   */
  @Test
  public void testPrintableAttribute() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#classAttribute()}.
   */
  @Test
  public void testClassAttribute() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#methodAttribute()}.
   */
  @Test
  public void testMethodAttribute() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#methodSpecification()}.
   */
  @Test
  public void testMethodSpecification() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#emptyspec()}.
   */
  @Test
  public void testEmptyspec() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#exname()}.
   */
  @Test
  public void testExname() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#specCase()}.
   */
  @Test
  public void testSpecCase() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#inCodeAttribute()}.
   */
  @Test
  public void testInCodeAttribute() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#assertspec()}.
   */
  @Test
  public void testAssertspec() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#modifyList()}.
   */
  @Test
  public void testModifyList() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#modifyExpression()}.
   */
  @Test
  public void testModifyExpression() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#modifySubExpr()}.
   */
  @Test
  public void testModifySubExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#specArray()}.
   */
  @Test
  public void testSpecArray() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#formula()}.
   */
  @Test
  public void testFormula() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#expression()}.
   */
  @Test
  public void testExpression() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#uncheckedExpression()}.
   */
  @Test
  public void testUncheckedExpression() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#conditionalExpression()}.
   */
  @Test
  public void testConditionalExpression() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#equivalenceExpr()}.
   */
  @Test
  public void testEquivalenceExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#impliesExpr()}.
   */
  @Test
  public void testImpliesExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#logicalOrExpr()}.
   */
  @Test
  public void testLogicalOrExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#logicalAndExpr()}.
   */
  @Test
  public void testLogicalAndExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#bitwiseOrExpr()}.
   */
  @Test
  public void testBitwiseOrExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#bitwiseXorExpr()}.
   */
  @Test
  public void testBitwiseXorExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#bitwiseAndExpr()}.
   */
  @Test
  public void testBitwiseAndExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#equalityExpr()}.
   */
  @Test
  public void testEqualityExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#relationalExpr()}.
   */
  @Test
  public void testRelationalExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#shiftExpr()}.
   */
  @Test
  public void testShiftExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#additiveExpr()}.
   */
  @Test
  public void testAdditiveExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#multExpr()}.
   */
  @Test
  public void testMultExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#quantifiedFormula()}.
   */
  @Test
  public void testQuantifiedFormula() {
    String[] paramdecls = { "\\forall int i ; true",
                            "\\exists int i; true",
                            "\\forall int i; i == i",
                            "\\forall int i; i != i"
    };
    String[] answers = {
                        "\\forall int i ; true",
                        "\\exists int i ; true",
                        "\\forall int i ; i == i",
                        "\\forall int i ; i != i"
    };
    System.out.println("testQuantifiedFormula: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      BMLParser parser = new BMLParser(tokens);
      quantifiedFormula_return ret;
      try {
        ret = parser.quantifiedFormula(); //initialisation of env
        assertEquals("quantified formula: " + i, ret.tree.toStringTree(),
                     answers[i]);
      } catch (RecognitionException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    System.out.println("testQuantifiedFormula end");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#dotExpr()}.
   */
  @Test
  public void testDotExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#primaryExpr()}.
   */
  @Test
  public void testPrimaryExpr() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#localVar()}.
   */
  @Test
  public void testLocalVar() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.BMLParser#ident()}.
   */
  @Test
  public void testIdent() {
    fail("Not yet implemented");
  }

}
