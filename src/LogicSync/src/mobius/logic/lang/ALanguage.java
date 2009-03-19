package mobius.logic.lang;

import java.io.File;
import java.util.List;

public abstract class ALanguage {
  /**
   * Check if a given file is written in this language.
   * It is supposed to primarily check the extension. 
   * @param f the file to check
   * @return true if the file is supposed to be 
   *  written in the current language
   */
  public abstract boolean isLanguageFile(File f);

  /**
   * The file will be used by the language as a source file.
   * @param in the file to use (it exists).
   */
  public abstract void addInput(File in);

  /**
   * The language will generate its output to this file and do a merge.
   * @param merge the file with which to merge
   */
  public abstract void addMerge(File merge);

  /**
   * The language will generate its output to the file,  and overwrite any 
   * previous content.
   * @param gen the file to output to
   */
  public abstract void addGenerate(File gen);

  /**
   * Prepare the language (it can parse the given input for instance).
   */
  public abstract void prepare();

  /**
   * Generate the files and merge the selected files.
   */
  public abstract void generate();
  
  /**
   * Right now the tool is not supposed to handle logics splitted in
   * multiple files.
   * @param list the list of files.
   */
  public void moreThanOneFileError(List<File> list) {
    System.err.println("At this moment the " + this + " cannot " +
                       "treat more than one file!\nGot:" + list + 
                       "\nDoing nothing :(");
  }
  

}
