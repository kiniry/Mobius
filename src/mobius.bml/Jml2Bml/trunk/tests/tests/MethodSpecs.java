package tests;
import java.io.IOException;

import jml2bml.exceptions.NotTranslatedException;

import org.junit.Test;
import org.kohsuke.args4j.CmdLineException;

import annot.io.ReadAttributeException;

public class MethodSpecs extends AbstractTests{
  @Test
  public void simpleAdd() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("methodspecs", "Test1");
  }

  @Test
  public void overloadMethod() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("methodspecs", "Test2");
  }

  @Test
  public void abstractMethod() throws ClassNotFoundException,
      ReadAttributeException, NotTranslatedException, IOException, CmdLineException {
    test("methodspecs", "Test3");
  }
}
