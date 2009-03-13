package mobius.bico.clops;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface BicoOptionsInterface {


 /* Option Help.
  * Description: Show the help message.
  * Aliases: [-h, --help]
  */

  /**
   * @return true if the option Help has been used
   * in the command line.
   */
  boolean isHelpSet();
  
  /**
   * Get the value of {@code Option} Help.
   * @return the value of the option Help if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getHelp();
  

 /* Option Dir.
  * Description: Specify directory in which Bico does its job (there must 
  		   be only one directory, and this argument is mandatory).
  * Aliases: []
  */

  /**
   * @return true if the option Dir has been used
   * in the command line.
   */
  boolean isDirSet();
  
  /**
   * Get the value of {@code Option} Dir.
   * @return the value of the option Dir if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getDir();
  

 /* Option Clazz.
  * Description: Generates also the file for the specified classes, bico must be able 
           to find them in its class path.
  * Aliases: []
  */

  /**
   * @return true if the option Clazz has been used
   * in the command line.
   */
  boolean isClazzSet();
  
  /**
   * Get the value of {@code Option} Clazz.
   * @return the value of the option Clazz if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.util.List<String> getClazz();
  

 /* Option Output.
  * Description: Used to specify the output directory.
  * Aliases: [-o]
  */

  /**
   * @return true if the option Output has been used
   * in the command line.
   */
  boolean isOutputSet();
  
  /**
   * Get the value of {@code Option} Output.
   * @return the value of the option Output if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getOutput();
  

 /* Option Map.
  * Description: Triggers the generation of the map implementation.
  * Aliases: [-m, --map]
  */

  /**
   * @return true if the option Map has been used
   * in the command line.
   */
  boolean isMapSet();
  
  /**
   * Get the value of {@code Option} Map.
   * @return the value of the option Map if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getMap();
  

 /* Option List.
  * Description: Triggers the generation of the list implementation.
  * Aliases: [-l, --list]
  */

  /**
   * @return true if the option List has been used
   * in the command line.
   */
  boolean isListSet();
  
  /**
   * Get the value of {@code Option} List.
   * @return the value of the option List if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getList();
  

 /* Option Lib.
  * Description: Enables the java.lang library generation. 
 		   It implies the generation of most of the JRE.
  * Aliases: [-lib]
  */

  /**
   * @return true if the option Lib has been used
   * in the command line.
   */
  boolean isLibSet();
  
  /**
   * Get the value of {@code Option} Lib.
   * @return the value of the option Lib if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getLib();
  

 /* Option ClassPath.
  * Description: Specifies the base working class path.
  * Aliases: [-cp]
  */

  /**
   * @return true if the option ClassPath has been used
   * in the command line.
   */
  boolean isClassPathSet();
  
  /**
   * Get the value of {@code Option} ClassPath.
   * @return the value of the option ClassPath if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getClassPath();
  
}
