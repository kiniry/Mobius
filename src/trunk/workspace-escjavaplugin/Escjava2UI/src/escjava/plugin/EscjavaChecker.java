/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package escjava.plugin;

import java.io.PrintStream;
import java.util.List;

import javafe.genericfile.GenericFile;
import javafe.util.Location;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;

import pluginlib.Log;
import pluginlib.Utils;

/**
 * This class is the glue between the plugin and the
 * escjava2 non-Eclipse code to do the checking
 * 
 * @author David R. Cok
 */

public class EscjavaChecker extends escjava.Main 
				implements javafe.util.ErrorSet.Reporter {

	/** The project on whose files the checker is acting */
	private IJavaProject project;
	
	/** An instance of the standard reporter */
	final private javafe.util.ErrorSet.Reporter oldReporter
		 = new javafe.util.ErrorSet.StandardReporter();
	/**
	 * The default constructor for the Escjava checker.
	 * @param project The Java project to which this instance will be applied.
	 */
	public EscjavaChecker(IJavaProject project) {
		super();
		this.project = project;
		// The following is not thread-safe - FIXME 
		javafe.util.ErrorSet.setReporter(this);
	}
	
	private String simplifyloc;
	
	/**
	 * Called by the EscJava infrastructure to report problems found
	 * in the analyzed code.
	 * @param severity  The problem severity - FIXME
	 * @param loc The Esc/Java Location of the problem
	 * @param length The length in characters of the region to be high-lighted
	 * @param message The problem description
	 * 
	 * @see javafe.util.ErrorSet.Reporter#report(int, int, int, java.lang.String)
	 */
	public void report(int severity, int loc, int length,
						String message) {
	  if (message.indexOf("Simplify") != -1) {
	    Utils.showMessageInUI(null,"Simplify problem",
	        "Could not invoke Simplify.  Check to be sure that "
	        + simplifyloc + " exists and is EXECUTABLE.");
	  }
	  if (!Options.quiet.getValue()) oldReporter.report(severity,loc,length,message);
    
		String filename = null;
		int line = 0;
		int cpos = 0;
		if (loc != Location.NULL) {
			GenericFile f = Location.toFile(loc);
			filename = f.getHumanName();
			if (f instanceof java.io.File) {
				filename = ((java.io.File)f).getAbsolutePath();
			}
			line = Location.toLineNumber(loc);
			cpos = Location.toOffset(loc);
		}
		IProject p = null;
		try {
			p = project.getProject();
			
			EscjavaPlugin.getPlugin().fireEscjavaFailed(
					p,
					filename,
					line,
					cpos-1,
					length,
					message,
					IEscjavaListener.ERROR); // FIXME - how to translate errors?
		} catch (Exception e) {
			Log.errorlog("Failed to translate error for Java project " + project.getElementName(),e);
		}
	}
	
	/**
	 * Translates additional information about an error into marker
	 * information; called by EscJava when a warning with associated
	 * information occurs.
	 * 
	 * @param loc  An EscJava Location value
	 * @param cp   An EscJava clip policy
	 * @see javafe.util.ErrorSet.Reporter#reportAssociatedInfo2(int, javafe.util.ClipPolicy)
	 */
	public void reportAssociatedInfo2(int loc, javafe.util.ClipPolicy cp) {
	  if (!Options.quiet.getValue()) oldReporter.reportAssociatedInfo2(loc,cp);
		reportHelper(loc);
	}
	
	/**
	 * Translates additional information about an error into marker
	 * information; called by EscJava when a warning with associated
	 * information occurs.
	 * 
	 * @param loc  An EscJava Location value
	 * @see javafe.util.ErrorSet.Reporter#reportAssociatedInfo2(int, javafe.util.ClipPolicy)
	 */
	public void reportAssociatedInfo(int loc) {
    if (!Options.quiet.getValue()) oldReporter.reportAssociatedInfo(loc);
		reportHelper(loc);
	}
	
	/**
	 * A local helper method that translates an Escjava
	 * Location value into additional declaration information
	 * in a Marker
	 * @param loc The EscJava Location value of a specification declaration
	 */
	private void reportHelper(int loc) {
		String f = Location.toFile(loc).getHumanName();
		try {
			EscjavaMarker.addMarkerInfo(f +" " + Location.toLineNumber(loc) + " " + Location.toOffset(loc));
		} catch (CoreException e) {
			Log.errorlog("An internal error occurred while trying to record additional information on a Marker",e);
			// Log and ignore the error
		}
	}

	/**
	 * The main method of this class. Provides the interface to invoke the
	 * checker on the specified inputs.
	 * 
	 * @param inputs The inputs (List of String) upon which the Escjava checker will be invoked
	 * @return true if the checker ran successfully, false if there were warnings
	 */
	public boolean run(List inputs) {
	  if (inputs.size() == 0) return true;
	  //escjava.parser.JMLParser.setClassPath(Utils.getProjectClassPathEntries(project));
	  //escjava.parser.JMLParser.parse(project,inputs);
	  if (Log.on) Log.log("Running Escjava checker");
	  if (!EscjavaUtils.isSpecsInstalled(project)) {
	    EscjavaUtils.installDefaultSpecs(project);
	  }
	  
	  inputs.add("-classpath");
	  inputs.add(Utils.getProjectClassPath(project));
	  
	  // FIXME - can avboid getting simplify if we are not doing any static checking
	  
	  String loc;
	  try {
	    if (Options.internalSimplify.getValue()) {
	      String os = Options.os.getStringValue();
	      loc = EscjavaUtils.findInternalSimplify(os);
	      if (loc == null) {
	        Utils.showMessageInUI(null, "Esc/Java",
	        "Could not locate a Simplify executable - see error log");
	        Log.errorlog(
	            "Could not locate a Simplify executable in the plugin: os = "
	            + System.getProperty("os.name"), null);
	        return false;
	      }
	    } else {
	      loc = Options.simplify.getValue();
	    }
	  } catch (Exception e) {
	    Utils.showMessageInUI(null,"Esc/Java",
	      "Could not locate a Simplify executable - see error log");
	    Log.errorlog("Could not locate a Simplify executable in the plugin",e);
	    return false;
	  }
	  inputs.add("-simplify");
	  inputs.add(loc);
	  simplifyloc = loc;
	  if (Log.on) Log.log("Using simplify executable at " + loc);
	  Options.getOptions(inputs);
	  
	  //		System.out.print("STARTING ESCJAVA WITH");
	  //		java.util.Iterator it = inputs.iterator();
	  //		while (it.hasNext()) {
	  //			System.out.print(" ");
	  //			System.out.print(it.next());
	  //		}
	  //		System.out.println("");
	  //		System.out.println("CLASSPATH " + Utils.getProjectClassPath(project));
	  
	  // This method is inherited from org.jmlspecs.checker.Main. Set the initial
	  // task to be executed by the compiler (Parsing in this case).
	  PrintStream out = System.out;
	  PrintStream err = System.err;
	  PrintStream newout = Log.logPrintStream();
	  System.setOut(newout);
	  System.setErr(newout);
	  int i = compile((String[])inputs.toArray(new String[0]));
	  System.setOut(out);
	  System.setErr(err);
	  if (Log.on) Log.log("Escjava checker ended, status code " + i);
	  return i == 0;
	}
}
