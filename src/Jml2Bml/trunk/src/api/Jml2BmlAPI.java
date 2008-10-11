package api;

import annot.io.ReadAttributeException;
import jml2bml.bytecode.ClassFileLocation;
import main.Main;

public class Jml2BmlAPI {
  public static void compile(final String sourceFile, final String outputDir,
                             final String classFile) throws ClassNotFoundException, ReadAttributeException  {
    new Main().compile(sourceFile, new ClassFileLocation(outputDir, classFile));
  }
}
