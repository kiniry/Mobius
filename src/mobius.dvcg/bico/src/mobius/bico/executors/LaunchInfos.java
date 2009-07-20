package mobius.bico.executors;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.implem.IImplemSpecifics;
import mobius.bico.implem.ListImplemSpecif;
import mobius.bico.implem.MapImplemSpecif;

import org.apache.bcel.util.ClassPath;

/**
 * A structure to handle informations to launch an executor.
 * Basically, it packages all the infos needed by the constructor.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class LaunchInfos {
  /** Specify the implementation to use. */
  IImplemSpecifics fImplem;
  
  /** Whether or not the libraries shall be generated. */
  boolean fGenerateLibs;
  /** The current working dir. */
  File fBaseDir;
  /** The output directory. */ 
  File fTargetDir;
  /** The classpath to use. */
  ClassPath fClassPath;
  /** the list of classes to treat. */
  final List<String> fClassToTreat = new ArrayList<String>();
  
  /**
   * Construct an info structure.
   */
  public LaunchInfos() {
    fImplem = new MapImplemSpecif();
    fGenerateLibs = false;
  }
  
  /**
   * Prepare the infos by checking the null values and
   * changing them if necessary.
   */
  public void prepare() {
    if (fBaseDir == null) {
      fBaseDir = new File("");
    }
    if (fTargetDir == null) {
      fTargetDir = fBaseDir;
    }
    if (fClassPath == null) {
      fClassPath = new ClassPath(fBaseDir.getAbsolutePath() + 
                  File.pathSeparatorChar + ClassPath.getClassPath());
    }
  }
  
  /**
   * Set the class path of the structure.
   * @param classpath a string representation of the 
   * class path (uses standard class path conventions).
   */
  public void setClassPath(final String classpath) {
    fClassPath = new ClassPath(classpath);
  }
  
  /**
   * Sets the base directory only if it is not already set.
   * @param dir the directory to set.
   */
  public void setBaseDir(final File dir) {
    fBaseDir = dir;
  }
  
  /**
   * Sets the output directory.
   * The directory must already exist
   * @param dir the output directory
   */
  public void setTargetDir(final File dir) {
    fTargetDir = dir;
  }
  
  /**
   * Adds the given class to the pending classes to treat.
   * @param cl the class to add. It can be a class name or a file.
   */
  public void addClassToTreat(final String cl) {
    final File f = new File(cl);
    if ((f.exists()) || ((f.getParentFile() != null) &&
        f.getParentFile() .exists())) {
      fClassToTreat.add(f.getAbsolutePath()); 
    } 
    else  {
      // we suppose it's to be found in the class path
      fClassToTreat.add(cl); 
    }
  }
  
  /**
   * Enable library generation, by default it is turned off.
   */
  public void enableLibrariesGeneration() {
    fGenerateLibs = true;
  }
  
  /**
   * Set the implementation to be the list.
   * Not properly tested.
   */
  public void setListImplementation() {
    fImplem = new ListImplemSpecif();
  }
}
