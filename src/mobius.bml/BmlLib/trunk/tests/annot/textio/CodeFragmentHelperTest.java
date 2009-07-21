package annot.textio;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import annot.textio.CodeFragmentHelper;

public class CodeFragmentHelperTest {

  String dirname = "tests/annot/textio/";

  String[] filenames = {
      "Full.btc", "Nothing.btc"
  };

  String[] texts;

  String[] results;

  @Before
  public void setUp() throws Exception {
    texts = new String[filenames.length];
    results = new String[filenames.length];
    for (int i = 0; i < filenames.length; i++) {
      final byte[] buf = new byte[1024];
      File f = new File(dirname + filenames[i]);
      InputStream is = new FileInputStream(f);
      texts[i] = new String();
      while (is.available() > 0) {
        final int hm = (is.available() < 1024) ? is.available() : 1024;
        is.read(buf);
        texts[i] += new String(buf, 0, hm);
      }
      is.close();
      f = new File(dirname + filenames[i] + "-res");
      is = new FileInputStream(f);
      results[i] = new String();
      while (is.available() > 0) {
        final int hm = (is.available() < 1024) ? is.available() : 1024;
        is.read(buf);
        results[i] += new String(buf, 0, hm);
      }
      is.close();
    }
  }

  @After
  public void tearDown() throws Exception {
  }

  @Test
  public void testPreProcess() {
    for (int i = 0; i < filenames.length; i++) {
      final String result = CodeFragmentHelper.preProcess(texts[i]);
      for (int j = 0; j < result.length(); j++) {
        assertSame("file " + i + " char " + j, result.charAt(j), results[i]
            .charAt(j));
      }
      assertTrue("for " + filenames[i], result.equals(results[i]));
    }
  }

}
