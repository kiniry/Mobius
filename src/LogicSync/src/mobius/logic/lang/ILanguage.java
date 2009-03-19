package mobius.logic.lang;

import java.io.File;

public interface ILanguage {
  /**
   * Check if a given file is written in this language.
   * It is supposed to primarily check the extension. 
   * @param f the file to check
   * @return true if the file is supposed to be 
   *  written in the current language
   */
  boolean isLanguageFile(File f);

  /**
   * The file will be used by the language as a source file.
   * @param in the file to use (it exists).
   */
  void addInput(File in);

  /**
   * The language will generate its output to this file and do a merge.
   * @param merge the file with which to merge
   */
  void addMerge(File merge);

  /**
   * The language will generate its output to the file,  and overwrite any 
   * previous content.
   * @param gen the file to output to
   */
  void addGenerate(File gen);

  /**
   * Prepare the language (it can parse the given input for instance).
   */
  void prepare();

  /**
   * Generate the files and merge the selected files.
   */
  void generate();

}
