import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import jml2bml.bytecode.ClassFileLocation;
import jml2bml.exceptions.NotTranslatedException;
import main.Main;

import org.junit.Before;
import org.junit.Test;
import org.kohsuke.args4j.CmdLineException;

import annot.io.ReadAttributeException;

public class MethodSpecs {
  boolean areFilesEqual(File f1, File f2) throws IOException {
    if (f1.length() != f2.length())
      return false;
    InputStream i1 = new FileInputStream(f1);
    InputStream i2 = new FileInputStream(f2);
    int b1, b2;
    do {
      b1 = i1.read();
      b2 = i2.read();
    } while (b1 == b2 && b1 != -1);
    i1.close();
    i2.close();
    return b1 == -1;
  }

  public void compareOutput(ClassFileLocation shouldLoc, ClassFileLocation isLoc) throws IOException {
    File shouldFile = new File(shouldLoc.getClassFilePath());
    File isFile = new File(shouldLoc.getClassFilePath());
    assertEquals(areFilesEqual(shouldFile, isFile), true);
  }
  
  @Before public void setUp() { 
    File f = new File("tmp/out.class");
    if (f.exists()) f.delete(); 
  }

  @Test
  public void simpleAdd() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    String[] args = {"test_input/methodspecs", "Test1", "test_input/methodspecs/Test1.java", "-o", "tmp/out.class"};
    new Main().doMain(args);
    compareOutput(new ClassFileLocation("test_output/methodspecs", "Test1"),
                  new ClassFileLocation("tmp", "out"));
  }

  @Test
  public void overloadMethod() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    String[] args = {"test_input/methodspecs", "Test2", "test_input/methodspecs/Test2.java", "-o", "tmp/out.class"};
    new Main().doMain(args);
    compareOutput(new ClassFileLocation("test_output/methodspecs", "Test2"),
                  new ClassFileLocation("tmp", "out"));
  }

  @Test
  public void abstractMethod() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    String[] args = {"test_input/methodspecs", "Test3", "test_input/methodspecs/Test3.java", "-o", "tmp/out.class"};
    new Main().doMain(args);
    compareOutput(new ClassFileLocation("test_output/methodspecs", "Test3"),
                  new ClassFileLocation("tmp", "out"));
  }
}
