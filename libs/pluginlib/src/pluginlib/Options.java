/*
 * This file is part of the Daikon plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 9, 2004
 */
package pluginlib;

import pluginlib.AbstractPreference;
import pluginlib.Utils;

/**
 * This class holds (as static variables) the persistent options of
 * the program.
 * 
 * @author David R. Cok
 */
public class Options {
	private static final String MOBIUS_PLUGIN_LIB_ID = "mobius.pluginlib";

	/** A copy of the plugin's id */
	final private static String PLUGIN_LIB_ID = MOBIUS_PLUGIN_LIB_ID + ".";
	
	/** The option button corresponding to Eclipse logging. */
	static public AbstractPreference.BooleanOption logging = new AbstractPreference.BooleanOption(
			(PLUGIN_LIB_ID + "Logging"),
			false,
			"Enable Eclipse informational messages",
			"Turns on Eclipse progress and debug messages (in the Console windows)");

	/** The choice of using the console or System.out for logging */
	static final public AbstractPreference.BooleanOption useConsole = new AbstractPreference.BooleanOption(
			(PLUGIN_LIB_ID + "UseConsole"),
			true,
			"Log to the Eclipse console (rather than System.out)",
			"If logging is enabled, the output can be sent either to" + Utils.eol +
			"the Eclipse console (checked) or to the Java process's System.out (unchecked)." + Utils.eol +
			"Depending on the environment, the latter may appear in a terminal window, in the console" + Utils.eol +
			"of a parent Eclipse UI, or may be lost.");
	
	/** The choice to send informational output to the log file as well */
	static final public AbstractPreference.BooleanOption alsoLogInfo = new AbstractPreference.BooleanOption(
			(PLUGIN_LIB_ID + "AlsoLogInfo"),
			false,
			"Send informational output to the Log file also",
			"Informational output, if enabled, is sent to either the Console" + Utils.eol +
			"or to System.out per the choice above; it may in addition be" + Utils.eol +
			"recorded in the system log file (along with error message) if" + Utils.eol +
			"this choice is enabled.");
}
