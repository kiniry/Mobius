package jml2bml;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import jml2bml.exceptions.Jml2BmlException;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;

public class BCClassManager {
  private Map < String, BCClass > classes = new HashMap < String, BCClass >();

  private final String inputDir;

  private final String outputDir;

  public BCClassManager(final String inputDir, final String outputDir) {
    this.inputDir = inputDir;
    this.outputDir = outputDir;
  }

  public BCClass getBCClass(final String name) {
    if (classes.containsKey(name))
      return classes.get(name);

    String path = name.replace('.', File.separatorChar);
    String lastSegment = path
        .substring(path.lastIndexOf(File.separatorChar) + 1);
    String fileDir = inputDir + File.separator +
      ((path.lastIndexOf(File.separatorChar) > 0) ?
          path.substring(0, path.lastIndexOf(File.separatorChar)) :
          "");
    try {
      BCClass result = new BCClass(fileDir, lastSegment);
      classes.put(name, result);
      return result;
    } catch (ClassNotFoundException e) {
      throw new Jml2BmlException("Class " + name + " not found.");
    } catch (ReadAttributeException e) {
      throw new Jml2BmlException("Error while loading class " + name + ": "+e);
    }
  }
  
  public void saveAll() throws IOException{
    for (String name: classes.keySet()){
      final BCClass clazz = classes.get(name);
      
      String outputName = outputDir+File.separator+name.replace('.', File.separatorChar) + ".class";      
      clazz.saveToFile(outputName);
    }
  }
}
