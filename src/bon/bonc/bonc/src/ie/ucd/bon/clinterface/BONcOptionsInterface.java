package ie.ucd.bon.clinterface;

import java.util.List;
import java.io.File;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface BONcOptionsInterface {


// Option Print. 
// Aliases: [-p, --print]

  /**
   * @return true if the option Print has been used
   * in the command line.
   */
  boolean isPrintSet();

  /**
   * The enumeration type used to represent the string enum option.
   */
  static enum  Print {
    SYSO("SYSO"),    TXT("TXT"),    DOT("DOT"),    HTML("HTML"),    DIC("DIC"),    IIG("IIG"),    ICG("ICG"),    CL("CL"),    PICG("PICG"),    PIIG("PIIG");

    private final String[] matchStrings;
    private Print(final String... s) {
      matchStrings = s;
    }
    public String toString() {
      return matchStrings.toString();
    }
    /**
     * Returns the appropriate enum value for the given string
     * @param s one of the following strings: [[ie.ucd.clops.util.Pair@67a5fb5a, ie.ucd.clops.util.Pair@421906df, ie.ucd.clops.util.Pair@79123c5f, ie.ucd.clops.util.Pair@1c39bf12, ie.ucd.clops.util.Pair@132f4538, ie.ucd.clops.util.Pair@469695f, ie.ucd.clops.util.Pair@2484de3c, ie.ucd.clops.util.Pair@f1a47df, ie.ucd.clops.util.Pair@6648938, ie.ucd.clops.util.Pair@326cbecf]]
     * @return a valid Print member.
     */
    public static Print get(final String s) {
      for (Print value : Print.values()) {
        for (String m : value.matchStrings) {
          if (m.equalsIgnoreCase(s)) return value;
        }
      }
      return null;
    }
    
  }

  /**
   * Get the value of {@code Option} Print.
   * @return the value of the option Print if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  Print getPrint();
  

// Option PrintOutput. 
// Aliases: [-po, --print-output]

  /**
   * @return true if the option PrintOutput has been used
   * in the command line.
   */
  boolean isPrintOutputSet();

  /**
   * Get the value of {@code Option} PrintOutput.
   * @return the value of the option PrintOutput if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  File getPrintOutput();
  

// Option PrettyPrint. 
// Aliases: [-pp, --pretty-print]

  /**
   * @return true if the option PrettyPrint has been used
   * in the command line.
   */
  boolean isPrettyPrintSet();

  /**
   * Get the value of {@code Option} PrettyPrint.
   * @return the value of the option PrettyPrint if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPrettyPrint();
  

// Option PrintMan. 
// Aliases: [--print-man]

  /**
   * @return true if the option PrintMan has been used
   * in the command line.
   */
  boolean isPrintManSet();

  /**
   * Get the value of {@code Option} PrintMan.
   * @return the value of the option PrintMan if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPrintMan();
  

// Option PrintReadme. 
// Aliases: [--print-readme]

  /**
   * @return true if the option PrintReadme has been used
   * in the command line.
   */
  boolean isPrintReadmeSet();

  /**
   * Get the value of {@code Option} PrintReadme.
   * @return the value of the option PrintReadme if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPrintReadme();
  

// Option PrintBashCompletion. 
// Aliases: [--print-bash-completion]

  /**
   * @return true if the option PrintBashCompletion has been used
   * in the command line.
   */
  boolean isPrintBashCompletionSet();

  /**
   * Get the value of {@code Option} PrintBashCompletion.
   * @return the value of the option PrintBashCompletion if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getPrintBashCompletion();
  

// Option Help. 
// Aliases: [-h, --help]

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
  

// Option Time. 
// Aliases: [-t, --time]

  /**
   * @return true if the option Time has been used
   * in the command line.
   */
  boolean isTimeSet();

  /**
   * Get the value of {@code Option} Time.
   * @return the value of the option Time if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getTime();
  

// Option Typecheck. 
// Aliases: [-tc, --typecheck]

  /**
   * @return true if the option Typecheck has been used
   * in the command line.
   */
  boolean isTypecheckSet();

  /**
   * Get the value of {@code Option} Typecheck.
   * @return the value of the option Typecheck if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getTypecheck();
  

// Option Informal. 
// Aliases: [-i, --informal]

  /**
   * @return true if the option Informal has been used
   * in the command line.
   */
  boolean isInformalSet();

  /**
   * Get the value of {@code Option} Informal.
   * @return the value of the option Informal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getInformal();
  

// Option Formal. 
// Aliases: [-f, --formal]

  /**
   * @return true if the option Formal has been used
   * in the command line.
   */
  boolean isFormalSet();

  /**
   * Get the value of {@code Option} Formal.
   * @return the value of the option Formal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getFormal();
  

// Option CheckInformal. 
// Aliases: [-ci, --check-informal]

  /**
   * @return true if the option CheckInformal has been used
   * in the command line.
   */
  boolean isCheckInformalSet();

  /**
   * Get the value of {@code Option} CheckInformal.
   * @return the value of the option CheckInformal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getCheckInformal();
  

// Option CheckFormal. 
// Aliases: [-cf, --check-formal]

  /**
   * @return true if the option CheckFormal has been used
   * in the command line.
   */
  boolean isCheckFormalSet();

  /**
   * Get the value of {@code Option} CheckFormal.
   * @return the value of the option CheckFormal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getCheckFormal();
  

// Option CheckConsistency. 
// Aliases: [-cc, --check-consistency]

  /**
   * @return true if the option CheckConsistency has been used
   * in the command line.
   */
  boolean isCheckConsistencySet();

  /**
   * Get the value of {@code Option} CheckConsistency.
   * @return the value of the option CheckConsistency if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getCheckConsistency();
  

// Option Debug. 
// Aliases: [-d, --debug]

  /**
   * @return true if the option Debug has been used
   * in the command line.
   */
  boolean isDebugSet();

  /**
   * Get the value of {@code Option} Debug.
   * @return the value of the option Debug if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getDebug();
  

// Option ReadFromStdin. 
// Aliases: [-]

  /**
   * @return true if the option ReadFromStdin has been used
   * in the command line.
   */
  boolean isReadFromStdinSet();

  /**
   * Get the value of {@code Option} ReadFromStdin.
   * @return the value of the option ReadFromStdin if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getReadFromStdin();
  

// Option GenClassDic. 
// Aliases: [-gcd, --gen-class-dic]

  /**
   * @return true if the option GenClassDic has been used
   * in the command line.
   */
  boolean isGenClassDicSet();

  /**
   * Get the value of {@code Option} GenClassDic.
   * @return the value of the option GenClassDic if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getGenClassDic();
  

// Option Graph. 
// Aliases: [-g, --graph]

  /**
   * @return true if the option Graph has been used
   * in the command line.
   */
  boolean isGraphSet();

  /**
   * The enumeration type used to represent the string enum option.
   */
  static enum  Graph {
    ICG("ICG"),    IIG("IIG");

    private final String[] matchStrings;
    private Graph(final String... s) {
      matchStrings = s;
    }
    public String toString() {
      return matchStrings.toString();
    }
    /**
     * Returns the appropriate enum value for the given string
     * @param s one of the following strings: [[ie.ucd.clops.util.Pair@14cee41f, ie.ucd.clops.util.Pair@1ae2b9e5]]
     * @return a valid Graph member.
     */
    public static Graph get(final String s) {
      for (Graph value : Graph.values()) {
        for (String m : value.matchStrings) {
          if (m.equalsIgnoreCase(s)) return value;
        }
      }
      return null;
    }
    
  }

  /**
   * Get the value of {@code Option} Graph.
   * @return the value of the option Graph if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  Graph getGraph();
  

// Option Version. 
// Aliases: [-v, -version, --version]

  /**
   * @return true if the option Version has been used
   * in the command line.
   */
  boolean isVersionSet();

  /**
   * Get the value of {@code Option} Version.
   * @return the value of the option Version if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getVersion();
  

// Option SourceFiles. 
// Aliases: []

  /**
   * @return true if the option SourceFiles has been used
   * in the command line.
   */
  boolean isSourceFilesSet();

  /**
   * Get the value of {@code Option} SourceFiles.
   * @return the value of the option SourceFiles if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getSourceFiles();
  
}
