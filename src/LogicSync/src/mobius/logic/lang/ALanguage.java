package mobius.logic.lang;

import java.io.File;
import java.util.List;

import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;
import mobius.util.Logger;

/**
 * The main class use to represent a language handler.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
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
   * Generate the files from the specified AST.
   * @param ast the ast to generate from
   */
  public abstract void generateFrom(TypeCheckedAst ast);

  /**
   * Merges the files with the specified AST.
   * @param ast the ast to generate from
   */
  public abstract void mergeWith(GenericAst ast);
  
  /**
   * Extract the generic AST. 
   * It is used to check consistency, and to generate the generic AST.
   * @return The AST corresponding to the input file of the language
   */
  public abstract GenericAst extractGenericAst();
  
  /**
   * Returns the name of the language.
   * @return A single word representing the language; Coq for instance
   */
  public abstract String getName();
  /**
   * Right now the tool is not supposed to handle logics splitted in
   * multiple files.
   * @param list the list of files.
   */
  public void moreThanOneFileError(final List<File> list) {
    Logger.err.println("At this moment the " + this + " cannot " +
                       "treat more than one file!\nGot:" + list + 
                       "\nDoing nothing :(");
  }
  

}
