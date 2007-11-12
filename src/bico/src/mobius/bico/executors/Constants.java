package mobius.bico.executors;

import java.io.File;

public class Constants {

  /** path separator for the Window file system */
  public static final char PATH_SEPARATOR = File.separatorChar;
  public static final char LINUX_PATH_SEPARATOR = '/';
  public static final char JAVA_NAME_SEPARATOR = '.';
  
  /** constants representing options passed to  the entry point */
  public static final String OPTION_MAP = "-map";
  public static final String OPTION_LIST = "-list";
  /** the base working class path. */
  public static final String OPTION_LIB = "-lib";
  public static final String OPTION_EXT_LIB = "-ext";
  public static final String OPTION_HELP = "-help";
  
  
  /**  Coq syntax	 */
  public static final String SPACE = " ";
  public static final String MODULE = "Module";
  public static final String LOAD = "Load";
  public static final String END_MODULE = "End";
  public static final String REQ_EXPORT = "Require Export";
  public static final String EXPORT = "Export";
  public static final String REQ_IMPORT = "Require Import";
  public static final String IMPORT = "Import";
  public static final String DEFINITION = "Definition";
  public static final String END_DEFINITION = "End";
  public static final String ADD_LOAD_PATH = "Add LoadPath ";
  
  
  public static final String CLASS_SUFFIX = ".class";
}
