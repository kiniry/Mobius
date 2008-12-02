/**
 * 
 */
package annot.textio;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import bmllib.utils.BMLChangeException;

import annot.bcclass.BCClass;

/**
 * @author alx
 *
 */
public class CodeFragmentTest {


  String dirname = "tests/annot/textio/";

  String[] filenames = {
      "Question",
  };

  String[] filenames_btc = {
      "Question-req",
  };

  String[] texts;
  String[] texts_btc;
  
  BCClass[] classes;

  CodeFragment[] fragments;

  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    texts = new String[filenames.length];
    classes = new BCClass[filenames.length];
    fragments = new CodeFragment[filenames.length];
    for (int i = 0; i < filenames.length; i++) {
      final byte[] buf = new byte[1024];
      final File f = new File(dirname + filenames[i] + ".btc");
      final InputStream is = new FileInputStream(f);
      texts[i] = new String();
      while (is.available() > 0) {
        final int hm = (is.available() < 1024) ? is.available() : 1024;
        is.read(buf);
        texts[i] += new String(buf, 0, hm);
      }
      is.close();
      classes[i] = new BCClass(dirname, filenames[i]);
      fragments[i] = new CodeFragment(classes[i], texts[i]);
    }
    texts_btc = new String[filenames_btc.length];
    for (int i = 0; i < filenames_btc.length; i++) {
      final byte[] buf = new byte[1024];
      final File f = new File(dirname + filenames_btc[i] + ".btc");
      final InputStream is = new FileInputStream(f);
      texts_btc[i] = new String();
      while (is.available() > 0) {
        final int hm = (is.available() < 1024) ? is.available() : 1024;
        is.read(buf);
        texts_btc[i] += new String(buf, 0, hm);
      }
      is.close();
    }

  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#CodeFragment(annot.bcclass.BCClass, java.lang.String)}.
   */
  @Test
  public void testCodeFragment() {
    final CodeFragment cf = new CodeFragment(classes[0], texts[0]);
    assertEquals("code", cf.getCode(), texts[0]);
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#addChange(int, int, java.lang.String)}.
   */
  @Test
  public void testAddChange() {
    final CodeFragment cf = new CodeFragment(classes[0], texts[0]);
    try {
      cf.addChange(4518, 0, " requires true");
    } catch (BMLChangeException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    assertEquals("changed code:", cf.getCode(), texts_btc[0]);
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#getCode()}.
   */
  @Test
  public void testGetCode() {
    assertEquals(fragments[0].getCode(), texts[0]);
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#getErrMsg()}.
   */
  @Test
  public void testGetErrMsg() {
    assertEquals("empty error for fresh fragment",
                 fragments[0].getErrMsg(), "");
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#isCorrect()}.
   */
  @Test
  public void testIsCorrect() {
    assertTrue("correct for fresh fragment",
                 fragments[0].isCorrect());
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#modify(int, int, java.lang.String)}.
   */
  @Test
  public void testModify() {
    fail("Not yet implemented");
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#performChanges()}.
   */
  @Test
  public void testPerformChanges() {
    fragments[0].performChanges();
    assertTrue(fragments[0].isCorrect());
  }

  /**
   * Test method for {@link annot.textio.CodeFragment#resetChanges()}.
   */
  @Test
  public void testResetChanges() {
    fail("Not yet implemented");
  }

}
