package tests;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;


import org.junit.Before;
import org.kohsuke.args4j.CmdLineException;

import annot.io.ReadAttributeException;

import jml2bml.Main;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.exceptions.NotTranslatedException;

public abstract class AbstractTests {
  private boolean areFilesEqual(File f1, File f2) throws IOException {
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

  protected void compareOutput(final ClassFileLocation shouldLoc,
                             final ClassFileLocation isLoc) throws IOException {
    File shouldFile = new File(shouldLoc.getClassFilePath());
    File isFile = new File(isLoc.getClassFilePath());
    assertEquals(areFilesEqual(shouldFile, isFile), true);
  }

  @Before public void setUp() { 
    File f = new File("tmp/out.class");
    if (f.exists()) f.delete(); 
  }
  
  protected void test(String pkg, String testName) throws IOException, CmdLineException, ClassNotFoundException, ReadAttributeException, NotTranslatedException{
    String[] args = {"test_input/"+pkg, testName, "tests/tests/"+pkg+"/"+testName+".java", "-o", "tmp/out.class"};
    new Main().doMain(args);
    compareOutput(new ClassFileLocation("test_output/"+pkg, testName),
                  new ClassFileLocation("tmp", "out"));    
  }
}
