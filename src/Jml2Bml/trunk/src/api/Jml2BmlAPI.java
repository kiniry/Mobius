package api;

import java.io.IOException;

import annot.io.ReadAttributeException;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.exceptions.NotTranslatedException;
import main.Main;

public class Jml2BmlAPI {

  public static void compile(final String sourceFile, final String outputDir,
                             final String classFile)
    throws ClassNotFoundException, ReadAttributeException, IOException {
    try {
      new Main().compile(sourceFile,
                         new ClassFileLocation(outputDir, classFile));
    } catch (NotTranslatedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
}
