/*
 * This file is part of the ESCJava2 plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 9, 2004
 */
package escjava.plugin;

import java.util.List;

import mobius.escjava2.EscToolsActivator;
import mobius.util.plugin.Utils;
import mobius.util.plugin.APreference.BooleanOption;
import mobius.util.plugin.APreference.ChoiceOption;


/**
 * This class holds (as static variables) the persistent options of
 * the program.
 * 
 * @author David R. Cok
 */
public final class Options {
  
  public static final String[] WARNING_OPTIONS = {"ZeroDiv", "ArrayStore",
    "Assert", "Cast", "Reachable", "Inconsistent", "Constraint",
    "CLeak", "DecreasesBound", "Decreases", "Unreadable", "Undefined",
    "UndefinedNormalPost", "UndefinedExceptionalPost", "IndexNegative",
    "IndexTooBig", "Uninit", "ILeak", "Initially", "Deadlock",
    "LoopInv", "LoopObjInv", "ModExt", "Modifies", "NegSize",
    "NonNull", "NonNullInit", "NonNullResult", "Null", "Invariant",
    "OwnerNull", "Post", "Pre", "Race", "RaceAllNull", "Unenforcable",
    "Exception", "SpecificationException", "Deferred", "Writable" };


  /** The option button corresponding to Eclipse logging. */
  public static final BooleanOption logging = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".Logging"),
      true,
      "Enable Eclipse informational messages",
      "Turns on Eclipse progress and debug messages (in the Console windows)");

  /** The choice of using the console or System.out for logging. */
  public static final  BooleanOption useConsole = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".UseConsole"),
      true,
      "Log to the Eclipse console (rather than System.out)",
      "If logging is enabled, the output can be sent either to" + Utils.eol +
      "the Eclipse console (checked) or to the Java process's " +
      "System.out (unchecked)." + Utils.eol +
      "Depending on the environment, the latter may appear in a " +
      "terminal window, in the console" + Utils.eol +
      "of a parent Eclipse UI, or may be lost.");
  
  /** The choice to send informational output to the log file as well. */
  public static final BooleanOption alsoLogInfo = 
    new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".AlsoLogInfo"),
      false,
      "Send informational output to the Log file also",
      "Informational output, if enabled, is sent to either the Console" + Utils.eol +
      "or to System.out per the choice above; it may in addition be" + Utils.eol +
      "recorded in the system log file (along with error message) if" + Utils.eol +
      "this choice is enabled.");

  /**
   * The option button corresponding to the Quiet option,
   * but in the reverse sense.
   */
  public static final BooleanOption quiet = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".quiet"),
      false,
      "Disable ESC/Java informational messages",
      "Turns off progress and timing messages (in the Console windows) [JML --Quiet option]");

  /**
   * The option button corresponding to -typecheck, which does only
   * parsing and typechecking.
   */
  public static final BooleanOption typeCheckOnly = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".typeCheckOnly"),
      false,
      "Type check only (no static checking)",
      "[escjava -typecheck option]"); // FIXME

  /**
   * The option button corresponding to -parsePlus,
   * which turns on the parsing of expressions beginning with //+@ and /*+@.
   */
  public static final BooleanOption parsePlus = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".parsePlus"),
      false,
      "Enable parsing of //+@ and /*+@ annotations",
      "Escjava parses annotations beginning with //@, /*@, //-@, /*-@; " + Utils.eol +
      "with this option enabled it also parses those beginning with //+@ and /*+@;" + 
      Utils.eol +
      "JML parses those starting with //@, /*@, //+@, and /*+@. [escjava -parsePlus option]");

  /**
   * The option button corresponding to -noSemicolonWarnings,
   * which turns off warnings due to missing semicolons.
   */
  public static final BooleanOption noSemicolonWarnings = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".noSemicolonWarnings"),
      false,
      "No semicolon warnings",
      "Turns off warnings about missing semicolons at the ends of lines" + Utils.eol +
      "(The original Esc/Java did not require these, but JML does).");

  /**
   * Enables caution as well as warning messages to be produced,
   * corresponding to the inverse of the -nocaution option.
   */
  public static final BooleanOption cautionMessages = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".cautionMessages"),
      true,
      "Enable caution messages",
      "Enables caution as well as warning messages [-nocaution option]");

  /**
   * Enables counterexample information to be generated 
   * [-counterexample option].
   */
  public static final BooleanOption counterexample = new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".counterexample"),
      false,
      "Enables output of counterexample information",
      "Enables output of counterexample information when annotation " +
      "violation warnings are produced by the Esc/Java static checker " +
      "[-counterexample option]");

  /**
   * Enables counterexample information to be generated [-counterexample option].
   */
  public static final BooleanOption suggest = 
    new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".suggest"),
      false,
      "Enables output of suggestion information",
      "Enables output of suggestions that might correct " +
      "static warnings of possible annotation violations [-suggest option]");

  /**
   * Enables checking for the use of impure methods in annotations [-checkPurity option].
   */
  public static final BooleanOption checkPurity = 
    new BooleanOption(
      (EscjavaPlugin.PLUGIN_ID + ".checkPurity"),
      true,
      "Enables checking that annotations are pure",
      "Warnings are issued when an annotation contains an impure " +
      "method [-checkPurity option]");

  /**
   * This allows the setting of the Esc/Java -ea, -da, -eajava, -eajml options.
   */
  public static final ChoiceOption assertBehavior = 
    new ChoiceOption(
      (EscjavaPlugin.PLUGIN_ID + ".assertBehavior"),
      new String[]{"Ignore assert", "Java behavior", "JML behavior"},
      1,
      "Behavior of assert statement (Java 1.4)",
      "If Java version 1.4 or higher is enabled, then there is a choice " +
      "of behavior for assert statements:" + Utils.eol +
      "1) Ignore assert statements;" + Utils.eol +
      "2) Treat Java assert statements as the Java compiler does;" + Utils.eol +
      "3) Treat Java assert statements like JML assert statements.");

  /** The option widget corresponding to the choice of source version 
   *  compatibility (Java 1.3, Java 1.4 or Java Card 2.1) to be supported.
   */
  public static final ChoiceOption source = 
    new ChoiceOption(
      (EscjavaPlugin.PLUGIN_ID + ".source"),
      EscToolsActivator.JavaVersions.toStringList(),
      1,
      "Java source version",
      "The version of Java that is supported [JML --source option]");

  
  /** An array of options for the various static checker warnings,
   *  corrresponding to whether the warnings are enabled or disabled
   *  (i.e. the -nowarn option).
   */
  private static BooleanOption[] warningOptions;
  


  /** */
  private Options() { }  
  
  /** Initializes, if necessary, and returns the array of options
   * corresponding to static warnings (each of which indicates whether
   * the corresponding warning is enabled or disabled).
   * 
   * @return The array of static checking warning options
   */
  //@ modifies warningOptions;
  //@ ensures \result != null;
  //@ ensures \result == warningOptions;
  public static BooleanOption[] warningOptions() {
    if (warningOptions == null) {
      initWarningOptions();
    }
    return warningOptions;
  }
  
  /**
   * Creates and initializes the array of warning options.
   */
   //@ ensures warningOptions != null;
  private static void initWarningOptions() {
    final String[] wnames = Options.WARNING_OPTIONS;
    final int n = wnames.length;
    warningOptions = new BooleanOption[n];

    for (int i = 0; i < n; ++i) {
      final boolean def = !(wnames[i].equals("Deadlock"));
      warningOptions[i] = new BooleanOption(
          (EscjavaPlugin.PLUGIN_ID + ".EscjavaWarning-" + wnames[i]),
          def,
          wnames[i],
          ""); // FIXME - tooltip
    }  
  }
  
  /** 
   * Fills in the command-line arguments according to the
   * values of the stored properties.
   * @param args  The command-line argument array to be added to
   *        (a List of String)
   */
  public static void getOptions(final List<String> args) {
    if (quiet.getValue()) {
      args.add("-quiet");
    }
    if (parsePlus.getValue()) {
      args.add("-parsePlus");
    }
    if (noSemicolonWarnings.getValue()) {
      args.add("-noSemicolonWarnings");
    }
    if (!cautionMessages.getValue()) {
      args.add("-noCautions");
    }
    if (typeCheckOnly.getValue()) {
      args.add("-typecheck");
    }
    if (counterexample.getValue()) {
      args.add("-counterexample");
    }
    if (suggest.getValue()) {
      args.add("-suggest");
    }
    if (checkPurity.getValue()) {
      args.add("-checkPurity");
    }
    args.add("-source"); 
    args.add(source.getStringValue());
    
    switch (assertBehavior.getIndexValue()) {
      case 0:
        args.add("-da");
        break;
      case 1:
        args.add("-eajava");
        break;
      case 2:
        args.add("-eajml");
        break;
      default:
        break;
    }
    
    if (warningOptions == null) {
      initWarningOptions();
    }

    for (BooleanOption b: warningOptions) {
      if (!b.getValue()) {
        args.add("-nowarn");
        args.add(b.label());
      }
    }
  }
  

}
