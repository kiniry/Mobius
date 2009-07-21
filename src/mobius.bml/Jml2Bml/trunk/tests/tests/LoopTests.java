package tests;
import java.io.IOException;

import jml2bml.exceptions.NotTranslatedException;

import org.junit.Test;
import org.kohsuke.args4j.CmdLineException;

import annot.io.ReadAttributeException;

public class LoopTests extends AbstractTests{
  @Test
  public void singleFor() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test1");
  }

  @Test
  public void singleEnhancedFor() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test2");
  }

  @Test
  public void infiniteFor() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test3");
  }

  @Test
  public void infiniteWhile() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test4");
  }

  @Test
  public void singleWhile() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test5");
  }

  @Test
  public void infiniteDoWhile() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test6");
  }

  @Test
  public void simpleDoWhile() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test7");
  }
  
  @Test
  public void doubleFor() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test8");
  }

  @Test
  public void whileBreak() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test9");
  }

  @Test
  public void whileContinue() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test10");
  }

  @Test
  public void forWhileBreakToLabel() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test11");
  }

  @Test
  public void trippleForBreakToLabel() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test12");
  }

  @Test
  public void forInTryCatch() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test13");
  }

  @Test
  public void forWhileTryCatchFinally() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test14");
  }

  @Test
  public void manyForsManyLabelsManyBreaks() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("loops", "Test15");
  }
}
