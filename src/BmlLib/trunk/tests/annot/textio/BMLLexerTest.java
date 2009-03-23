/**
 * 
 */
package annot.textio;

import static org.junit.Assert.*;

import java.util.List;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;


/**
 * @author alx
 *
 */
public class BMLLexerTest {

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
   * Test method for {@link annot.textio.BMLLexer#mIDENT()}.
   */
  @Test
  public void testMIDENT() {
    String[] paramdecls = { "ala",
                            "Ala",
                            "alAma",
                            "aka1",
                            "aka1231"
                            };
    String[] answers = { "ala",
                         "Ala",
                         "alAma",
                         "aka1",
                         "aka1231"
                         };
    System.out.println("testMIDENT: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      List l = tokens.getTokens();
      assertEquals("IDENT type test " + i + ":", BMLLexer.IDENT,
                   ((Token)l.get(0)).getType());
      assertEquals("IDENT test " + i + ":", answers[i], tokens.toString(0, 0));
    }
    System.out.println("testMIDENT end");
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mNAT()}.
   */
  @Test
  public void testMNAT() {
    String[] paramdecls = { "1000",
                            "0",
                            "10"
                            };
    String[] answers = { "1000",
                         "0",
                         "10"
                         };
    System.out.println("testMNAT: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      assertEquals("NAT test " + i + ":", answers[i], tokens.toString(0, 0));
    }
    System.out.println("testMNATL end");
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mNATL()}.
   */
  @Test
  public void testMNATL() {
    String[] paramdecls = { "1000L;",
                            "0L;",
                            "10L;"
                            };
    String[] answers = { "1000L",
                         "0L",
                         "10L"
                         };
    System.out.println("testMNATL: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      List l = tokens.getTokens();
      assertEquals("NATL type test " + i + ":", BMLLexer.NATL,
                   ((Token)l.get(0)).getType());
      assertEquals("NATL type test " + i + ":", answers[i],
                   ((Token)l.get(0)).getText());
    }
    System.out.println("testMNATL end");
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mSTRING()}.
   */
  @Test
  public void testMStringLiteral() {
    String[] paramdecls = { "\"I have just completed the test! My score was: \"",
                            "\"\"",
                            "\"\" "
                            };
    String[] answers = { "\"I have just completed the test! My score was: \"",
                         "\"\"",
                         "\"\""
                         };
    System.out.println("testMSTRING: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      List l = tokens.getTokens();
//      assertEquals("STRING type test " + i + ":", BMLLexer.StringLiteral,
//                   ((Token)l.get(0)).getType());
      assertEquals("STRING type test " + i + ":", answers[i],
                   ((Token)l.get(0)).getText());
    }
    System.out.println("testMSTRING end");
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mWS()}.
   */
  @Test
  public void testMWS() {
    String[] paramdecls = { "\t\t",
                            "   \t   ",
                            "\t\n\t"
                            };
    String[] answers = { "\t",
                         " ",
                         "\t"
                         };
    System.out.println("testMWS: -----------------");
    for (int i = 0; i < paramdecls.length; i++) {
      final CharStream chstr = new ANTLRStringStream(paramdecls[i]);
      final BMLLexer lex = new BMLLexer(chstr);
      final CommonTokenStream tokens = new CommonTokenStream(lex);
      List l = tokens.getTokens();
      assertEquals("WS type test " + i + ":", BMLLexer.WS,
                   ((Token)l.get(0)).getType());
      assertEquals("WS test " + i + ":", answers[i], tokens.toString(0, 0));
    }
    System.out.println("testMWS end");
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mEOF()}.
   */
  @Test
  public void testMEOF() {
    final CharStream chstr = new ANTLRStringStream("\n");
    final BMLLexer lex = new BMLLexer(chstr);
    final CommonTokenStream tokens = new CommonTokenStream(lex);
    //List l = tokens.getTokens();
    Token t1 = tokens.LT(1);
    tokens.consume();
    Token t2 = tokens.LT(1);
    assertNotSame("EOF test neq:", BMLLexer.EOF, t1.getType());
    assertEquals("EOF test eq:", BMLLexer.EOF, t2.getType());
  }

  /**
   * Test method for {@link annot.textio.BMLLexer#mEOL()}.
   */
  @Test
  public void testMEOL() {
    final CharStream chstr = new ANTLRStringStream("\n ala");
    final BMLLexer lex = new BMLLexer(chstr);
    final CommonTokenStream tokens = new CommonTokenStream(lex);
    List l = tokens.getTokens();
    assertEquals("EOL test eq:", BMLLexer.EOL, ((Token)l.get(0)).getType());
    assertNotSame("EOL test neq:", BMLLexer.EOL, l.get(0));
  }

}
