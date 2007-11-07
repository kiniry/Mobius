/*
 * This file is part of the Daikon plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 9, 2004
 */
package escjava.plugin;

import java.util.List;

import pluginlib.AbstractPreference;
import pluginlib.Utils;

/**
 * This class holds (as static variables) the persistent options of
 * the program.
 * 
 * @author David R. Cok
 */
public class Options {
	/** A copy of the plugin's id */
	final private static String PLUGINID = EscjavaPlugin.UI_PLUGIN_ID + ".";
	
	/** The option button corresponding to Eclipse logging. */
	static public AbstractPreference.BooleanOption logging = new AbstractPreference.BooleanOption(
			(PLUGINID + "Logging"),
			false,
			"Enable Eclipse informational messages",
			"Turns on Eclipse progress and debug messages (in the Console windows)");

	/** The choice of using the console or System.out for logging */
	static final public AbstractPreference.BooleanOption useConsole = new AbstractPreference.BooleanOption(
			(PLUGINID + "UseConsole"),
			true,
			"Log to the Eclipse console (rather than System.out)",
			"If logging is enabled, the output can be sent either to" + Utils.eol +
			"the Eclipse console (checked) or to the Java process's System.out (unchecked)." + Utils.eol +
			"Depending on the environment, the latter may appear in a terminal window, in the console" + Utils.eol +
			"of a parent Eclipse UI, or may be lost.");
	
	/** The choice to send informational output to the log file as well */
	static final public AbstractPreference.BooleanOption alsoLogInfo = new AbstractPreference.BooleanOption(
			(PLUGINID + "AlsoLogInfo"),
			false,
			"Send informational output to the Log file also",
			"Informational output, if enabled, is sent to either the Console" + Utils.eol +
			"or to System.out per the choice above; it may in addition be" + Utils.eol +
			"recorded in the system log file (along with error message) if" + Utils.eol +
			"this choice is enabled.");

	/**
	 * Whether to use the internal simplify.
	 */
	static final public AbstractPreference.BooleanOption internalSimplify =
	  new AbstractPreference.BooleanOption(
	      PLUGINID + "internalSimplify",
	      false,
	      "Use Internal Version",
	      "Use the Simplify executable internal to the plug-in"
	      );

	static final public AbstractPreference.ChoiceOption os = new AbstractPreference.ChoiceOption(
			(PLUGINID + "osname"),
			new String[]{"","Windows","Linux","MacOSX","Solaris"},
			0,
			"Internal Simplify Version",
			"The choice of internal version of Simplify (pick the host platform)");


	/**
	 * The Simplify executable to use (a value is required).
	 */
	static final public AbstractPreference.StringOption simplify = new AbstractPreference.StringOption(
			(PLUGINID + "simplify"), 
			"", 
			"External Simplify executable to use",
			"The static checker needs a version of the Simplify executable for" + Utils.eol +
			"this platform; it must be obtained indepenedently from either the" + Utils.eol +
			"Mobius website or the HP Labs website");
	/**
	 * The option button corresponding to the Quiet option,
	 * but in the reverse sense.
	 */
	static final public AbstractPreference.BooleanOption quiet = new AbstractPreference.BooleanOption(
			(PLUGINID + "quiet"),
			true,
			"Disable ESC/Java informational messages",
			"Turns off progress and timing messages (in the Console windows) [JML --Quiet option]");

	/**
	 * The option button corresponding to -typecheck, which does only
	 * parsing and typechecking.
	 */
	static final public AbstractPreference.BooleanOption typeCheckOnly = new AbstractPreference.BooleanOption(
			(PLUGINID + "typeCheckOnly"),
			false,
			"Type check only (no static checking)",
			"[escjava -typecheck option]"); // FIXME

	/**
	 * The option button corresponding to -parsePlus,
	 * which turns off warnings due to missing semicolons
	 */
	static final public AbstractPreference.BooleanOption parsePlus = new AbstractPreference.BooleanOption(
			(PLUGINID + "parsePlus"),
			false,
			"Enable parsing of //+@ and /*+@ annotations",
			"Escjava parses annotations beginning with //@, /*@, //-@, /*-@; " + Utils.eol +
			"with this option enabled it also parses those beginning with //+@ and /*+@;" + Utils.eol +
			"JML parses those starting with //@, /*@, //+@, and /*+@. [escjava -parsePlus option]");

	/**
	 * The option button corresponding to -noSemicolonWarnings,
	 * which turns off warnings due to missing semicolons
	 */
	static final public AbstractPreference.BooleanOption noSemicolonWarnings = new AbstractPreference.BooleanOption(
			(PLUGINID + "noSemicolonWarnings"),
			false,
			"No semicolon warnings",
			"Turns off warnings about missing semicolons at the ends of lines" + Utils.eol +
			"(The original Esc/Java did not require these, but JML does).");

	/**
	 * Enables caution as well as warning messages to be produced,
	 * correpsonding to the inverse of the -nocaution option
	 */
	static final public AbstractPreference.BooleanOption cautionMessages = new AbstractPreference.BooleanOption(
			(PLUGINID + "cautionMessages"),
			true,
			"Enable caution messages",
			"Enables caution as well as warning messages [-nocaution option]");

	/**
	 * Enables counterexample information to be generated [-counterexample option]
	 */
	static final public AbstractPreference.BooleanOption counterexample = new AbstractPreference.BooleanOption(
			(PLUGINID + "counterexample"),
			false,
			"Enables output of counterexample information",
			"Enables output of counterexample information when annotation violation warnings are produced by the Esc/Java static checker [-counterexample option]");

	/**
	 * Enables counterexample information to be generated [-counterexample option]
	 */
	static final public AbstractPreference.BooleanOption suggest = new AbstractPreference.BooleanOption(
			(PLUGINID + "suggest"),
			false,
			"Enables output of suggestion information",
			"Enables output of suggestions that might correct static warnings of possible annotation violations [-suggest option]");

	/**
	 * Enables checking for the use of impure methods in annotations [-checkPurity option]
	 */
	static final public AbstractPreference.BooleanOption checkPurity = new AbstractPreference.BooleanOption(
			(PLUGINID + "checkPurity"),
			true,
			"Enables checking that annotations are pure",
			"Warnings are issued when an annotation contains an impure method [-checkPurity option]");


	/** The option widget corresponding to the choice of source
	 *  version compatibility (Java 1.3 or Java 1.4) to be supported -
	 *  this is essentially the interpretation to be applied to the
	 *  assert keyword.
	 */
	static final protected AbstractPreference.ChoiceOption source = new AbstractPreference.ChoiceOption(
			(PLUGINID + "source"),
			new String[]{"1.3","1.4","1.5"},
			1,
			"Java source version",
			"The version of Java that is supported [JML --source option]");

	/**
	 * This allows the setting of the Esc/Java -ea, -da, -eajava, -eajml options.
	 */
	static final public AbstractPreference.ChoiceOption assertBehavior = new AbstractPreference.ChoiceOption(
			(PLUGINID + "assertBehavior"),
			new String[]{"Ignore assert","Java behavior","JML behavior"},
			1,
			"Behavior of assert statement (Java 1.4)",
			"If Java version 1.4 or higher is enabled, then there is a choice of behavior for assert statements:" + Utils.eol +
			"1) Ignore assert statements;" + Utils.eol +
			"2) Treat Java assert statements as the Java compiler does;" + Utils.eol +
			"3) Treat Java assert statements like JML assert statements.");

	/** An array of options for the various static checker warnings,
	 *  corrresponding to whether the warnings are enabled or disabled
	 *  (i.e. the -nowarn option).
	 */
	static private AbstractPreference.BooleanOption[] warningOptions;

	/** Initializes, if necessary, and returns the array of options
	 * corresponding to static warnings (each of which indicates whether
	 * the corresponding warning is enabled or disabled).
	 * 
	 * @return The aray of static chcking warning options
	 */
	//@ modifies warningOptions;
	//@ ensures \result != null;
	//@ ensures \result == warningOptions;
	static public AbstractPreference.BooleanOption[] warningOptions() {
		if (warningOptions == null) initWarningOptions();
		return warningOptions;
	}
	
	/**
	 * Creates and initializes the array of warning options
	 */
	//@ requires escjava.ast.TagConstants.escchecks.length > 4;
	//@ ensures warningOptions != null;
	private static void initWarningOptions() {
		String[] wnames = escjava.ast.TagConstants.escchecks;
		int n = wnames.length-4;
		warningOptions = new AbstractPreference.BooleanOption[n];

		for (int i=0; i<n; ++i) {
			boolean def = !(wnames[i].equals("Deadlock"));
			warningOptions[i] = new AbstractPreference.BooleanOption(
					(EscjavaPlugin.UI_PLUGIN_ID + ".EscjavaWarning-" + wnames[i]),
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
	public static void getOptions(List args) {
		if (quiet.getValue()) args.add("-quiet");
		if (parsePlus.getValue()) args.add("-parsePlus");
		if (noSemicolonWarnings.getValue()) args.add("-noSemicolonWarnings");
		if (!cautionMessages.getValue()) args.add("-noCautions");
		if (typeCheckOnly.getValue()) args.add("-typecheck");
		if (counterexample.getValue()) args.add("-counterexample");
		if (suggest.getValue()) args.add("-suggest");
		if (checkPurity.getValue()) args.add("-checkPurity");
		args.add("-source"); args.add(source.getStringValue());
		int i = assertBehavior.getIndexValue();
		if (i==0) args.add("-da");
		if (i==1) args.add("-eajava");
		if (i==2) args.add("-eajml");
		if (warningOptions == null) initWarningOptions();

		for (int k=0; k<warningOptions.length; ++k) {
			if (!warningOptions[k].getValue()) {
				args.add("-nowarn");
				args.add(warningOptions[k].label());
			}
		}
	}
	
	static {
	  if (os.getIndexValue() == 0) {
	    String osname = System.getProperty("os.name");
			if (osname.startsWith("Windows")) osname = "Windows";
			else if (osname.equals("linux")||
			         osname.equals("Linux")) osname = "Linux";
			else if (osname.equals("darwin")||
			         osname.equals("MacOSX")||
			         osname.equals("Mac OS X")) osname = "MacOSX";
			else if (osname.equals("solaris")||
			         osname.equals("Solaris")) osname = "Solaris";
	    os.setValue(osname);
	  }
	}
}
