package ie.ucd.bon.interface;

import java.util.List;
import java.io.File;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface BONcOptionsInterface {


// Option typecheck. 
// Aliases: [-tc, --typecheck]

  /**
   * @return true if the option typecheck has been used
   * in the command line.
   */
  boolean istypecheckSet();

  /**
   * Get the value of {@code Option} typecheck.
   * @return the value of the option typecheck if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean gettypecheck();
  

// Option no_typecheck. 
// Aliases: [-ntc, --no-typecheck]

  /**
   * @return true if the option no_typecheck has been used
   * in the command line.
   */
  boolean isno_typecheckSet();

  /**
   * Get the value of {@code Option} no_typecheck.
   * @return the value of the option no_typecheck if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getno_typecheck();
  

// Option print. 
// Aliases: [-p, --print]

  /**
   * @return true if the option print has been used
   * in the command line.
   */
  boolean isprintSet();

  /**
   * The enumeration type used to represent the string enum option.
   */
  enum  print {
    xhtml("xhtml"),    dic("dic"),    html("html"),    txt("txt");
    private final String[] matchStrings;
    private print(final String... s) {
      matchStrings = s;
    }
    public String toString() {
      return matchStrings.toString();
    }
    /**
     * Returns the appropriate enum value for the given string
     * @param s one of the following strings: [{xhtml="xhtml", dic="dic", html="html", txt="txt"}]
     * @return a valid print member.
     */
    public static print get(final String s) {
      for (print value : print.values()) {
        for (String m : value.matchStrings) {
          if (m.equalsIgnoreCase(s)) return value;
        }
      }
      return null;
    }
    
  }

  /**
   * Get the value of {@code Option} print.
   * @return the value of the option print if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  print getprint();
  

// Option print_output. 
// Aliases: [-po, --print-output]

  /**
   * @return true if the option print_output has been used
   * in the command line.
   */
  boolean isprint_outputSet();

  /**
   * Get the value of {@code Option} print_output.
   * @return the value of the option print_output if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  File getprint_output();
  

// Option pretty_print. 
// Aliases: [-pp, --pretty-print]

  /**
   * @return true if the option pretty_print has been used
   * in the command line.
   */
  boolean ispretty_printSet();

  /**
   * Get the value of {@code Option} pretty_print.
   * @return the value of the option pretty_print if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getpretty_print();
  

// Option help. 
// Aliases: [-h, --help]

  /**
   * @return true if the option help has been used
   * in the command line.
   */
  boolean ishelpSet();

  /**
   * Get the value of {@code Option} help.
   * @return the value of the option help if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean gethelp();
  

// Option hidden_help. 
// Aliases: [-hh, --hidden-help]

  /**
   * @return true if the option hidden_help has been used
   * in the command line.
   */
  boolean ishidden_helpSet();

  /**
   * Get the value of {@code Option} hidden_help.
   * @return the value of the option hidden_help if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean gethidden_help();
  

// Option time. 
// Aliases: [-t, --time]

  /**
   * @return true if the option time has been used
   * in the command line.
   */
  boolean istimeSet();

  /**
   * Get the value of {@code Option} time.
   * @return the value of the option time if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean gettime();
  

// Option informal. 
// Aliases: [-i, --informal]

  /**
   * @return true if the option informal has been used
   * in the command line.
   */
  boolean isinformalSet();

  /**
   * Get the value of {@code Option} informal.
   * @return the value of the option informal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getinformal();
  

// Option formal. 
// Aliases: [-f, --formal]

  /**
   * @return true if the option formal has been used
   * in the command line.
   */
  boolean isformalSet();

  /**
   * Get the value of {@code Option} formal.
   * @return the value of the option formal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getformal();
  

// Option check_informal. 
// Aliases: [-ci, --check-informal]

  /**
   * @return true if the option check_informal has been used
   * in the command line.
   */
  boolean ischeck_informalSet();

  /**
   * Get the value of {@code Option} check_informal.
   * @return the value of the option check_informal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getcheck_informal();
  

// Option check_formal. 
// Aliases: [-cf, --check-formal]

  /**
   * @return true if the option check_formal has been used
   * in the command line.
   */
  boolean ischeck_formalSet();

  /**
   * Get the value of {@code Option} check_formal.
   * @return the value of the option check_formal if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getcheck_formal();
  

// Option check_consistency. 
// Aliases: [-cc, --check-consistency]

  /**
   * @return true if the option check_consistency has been used
   * in the command line.
   */
  boolean ischeck_consistencySet();

  /**
   * Get the value of {@code Option} check_consistency.
   * @return the value of the option check_consistency if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getcheck_consistency();
  

// Option no_check_consistency. 
// Aliases: [-ncc, --no-check-consistency]

  /**
   * @return true if the option no_check_consistency has been used
   * in the command line.
   */
  boolean isno_check_consistencySet();

  /**
   * Get the value of {@code Option} no_check_consistency.
   * @return the value of the option no_check_consistency if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getno_check_consistency();
  

// Option debug. 
// Aliases: [-d, --debug]

  /**
   * @return true if the option debug has been used
   * in the command line.
   */
  boolean isdebugSet();

  /**
   * Get the value of {@code Option} debug.
   * @return the value of the option debug if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getdebug();
  

// Option gen_class_dic. 
// Aliases: [-gcd, --gen-class-dic]

  /**
   * @return true if the option gen_class_dic has been used
   * in the command line.
   */
  boolean isgen_class_dicSet();

  /**
   * Get the value of {@code Option} gen_class_dic.
   * @return the value of the option gen_class_dic if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getgen_class_dic();
  

// Option no_gen_class_dic. 
// Aliases: [-ngcd, --no-gen-class-dic]

  /**
   * @return true if the option no_gen_class_dic has been used
   * in the command line.
   */
  boolean isno_gen_class_dicSet();

  /**
   * Get the value of {@code Option} no_gen_class_dic.
   * @return the value of the option no_gen_class_dic if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getno_gen_class_dic();
  

// Option graph. 
// Aliases: [-g, --graph]

  /**
   * @return true if the option graph has been used
   * in the command line.
   */
  boolean isgraphSet();

  /**
   * The enumeration type used to represent the string enum option.
   */
  enum  graph {
    icg("icg"),    iig("iig");
    private final String[] matchStrings;
    private graph(final String... s) {
      matchStrings = s;
    }
    public String toString() {
      return matchStrings.toString();
    }
    /**
     * Returns the appropriate enum value for the given string
     * @param s one of the following strings: [{icg="icg", iig="iig"}]
     * @return a valid graph member.
     */
    public static graph get(final String s) {
      for (graph value : graph.values()) {
        for (String m : value.matchStrings) {
          if (m.equalsIgnoreCase(s)) return value;
        }
      }
      return null;
    }
    
  }

  /**
   * Get the value of {@code Option} graph.
   * @return the value of the option graph if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  graph getgraph();
  

// Option version. 
// Aliases: [-v, --version]

  /**
   * @return true if the option version has been used
   * in the command line.
   */
  boolean isversionSet();

  /**
   * Get the value of {@code Option} version.
   * @return the value of the option version if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getversion();
  

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
