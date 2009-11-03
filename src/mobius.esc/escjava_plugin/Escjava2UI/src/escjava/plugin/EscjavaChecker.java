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
import javafe.util.ClipPolicy;
import javafe.util.Location;
import mobius.prover.simplify.SimplifyEditor;
import mobius.util.plugin.Log;
import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;


/**
 * This class is the glue between the plugin and the
 * escjava2 non-Eclipse code to do the checking.
 * 
 * @author David R. Cok
 */

public class EscjavaChecker extends escjava.Main 
        implements javafe.util.ErrorSet.Reporter {

  public static final String COULD_NOT_LOCATE_SPECIFICATIONS_FOR = 
    "Could not locate specifications for ";

  /** The project on whose files the checker is acting. */
  private IJavaProject project;
  
  /** An instance of the standard reporter. */
  private final javafe.util.ErrorSet.Reporter oldReporter = 
    new javafe.util.ErrorSet.StandardReporter();
  
  /** the location of the simplify executable. */
  private String simplifyloc;
  
  /**
   * The default constructor for the Escjava checker.
   * @param proj The Java project to which this instance will be applied.
   */
  public EscjavaChecker(final IJavaProject proj) {
    super();
    project = proj;
    // The following is not thread-safe - FIXME 
    javafe.util.ErrorSet.setReporter(this);
  }
  

  
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
  public void report(final int severity, final int loc, 
                     final int length, final String message) {
    if (message.indexOf("Simplify") != -1) {
      Utils.showMessageInUI(null, "Simplify problem",
          "Could not invoke Simplify.  Check to be sure that " + 
          simplifyloc + " exists and is EXECUTABLE.");
    }
    if (!Options.quiet.getValue()) {
      oldReporter.report(severity, loc, length, message);
    }
    
    String filename = null;
    int line = 0;
    int cpos = 0;
    if (loc != Location.NULL) {
      final GenericFile f = Location.toFile(loc);
      filename = f.getHumanName();
      if (f instanceof java.io.File) {
        filename = ((java.io.File)f).getAbsolutePath();
      }
      line = Location.toLineNumber(loc);
      if (!Location.isWholeFileLoc(loc)) {
        cpos = Location.toOffset(loc);
      }
    }
    IProject p = null;
    try {
      p = project.getProject();
      
      EscjavaPlugin.getPlugin().fireEscjavaFailed(
          p,
          filename,
          line,
          cpos - 1,
          length,
          message,
          IEscjavaListener.ERROR); // FIXME - how to translate errors?
    } 
    catch (Exception e) {
      Log.errorlog("Failed to translate error for Java project " + 
                   project.getElementName(), e);
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
  public void reportAssociatedInfo2(final int loc, final ClipPolicy cp) {
    if (!Options.quiet.getValue()) {
      oldReporter.reportAssociatedInfo2(loc, cp);
    }
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
  public void reportAssociatedInfo(final int loc) {
    if (!Options.quiet.getValue()) {
      oldReporter.reportAssociatedInfo(loc);
    }
    reportHelper(loc);
  }
  
  /**
   * A local helper method that translates an Escjava
   * Location value into additional declaration information
   * in a Marker.
   * @param loc The EscJava Location value of a specification declaration
   */
  private void reportHelper(final int loc) {
    final String f = Location.toFile(loc).getHumanName();
    try {
      if (Location.isWholeFileLoc(loc)) {
        EscjavaMarker.addMarkerInfo(f + " " + Location.toLineNumber(loc)); 
      }
      else {
        EscjavaMarker.addMarkerInfo(f + " " + Location.toLineNumber(loc) + 
                                    " " + Location.toOffset(loc));
      }
    }
    catch (CoreException e) {
      Log.errorlog("An internal error occurred while trying to record " +
                   "additional information on a Marker", e);
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
  public boolean run(final List<String> inputs) {
    if (inputs.size() == 0) {
      return true;
    }
    //escjava.parser.JMLParser.setClassPath(Utils.getProjectClassPathEntries(project));
    //escjava.parser.JMLParser.parse(project,inputs);
    if (Log.on) {
      Log.log("Running Escjava checker");
    }
    if (!addSpecsOptions(inputs) || 
        !addClasspathOptions(inputs) || 
        !addSimplifyOptions(inputs)) {
      return false;
    }
    
    Options.getOptions(inputs);
    
    //    System.out.print("STARTING ESCJAVA WITH");
    //    java.util.Iterator it = inputs.iterator();
    //    while (it.hasNext()) {
    //      System.out.print(" ");
    //      System.out.print(it.next());
    //    }
    //    System.err.println("");
    //    System.err.println("CLASSPATH " + Utils.getProjectClassPath(project));
    
    // This method is inherited from org.jmlspecs.checker.Main. Set the initial
    // task to be executed by the compiler (Parsing in this case).
    final  PrintStream out = System.out;
    final  PrintStream err = System.err;
    final  PrintStream newout = Log.logPrintStream();
    System.setOut(newout);
    System.setErr(newout);
    final  String[] strings = new String[0];
    final  String[] inputArray = (String[])inputs.toArray(strings);
    final  int i = compile(inputArray);
    System.setOut(out);
    System.setErr(err);
    if (Log.on) {
      Log.log("Escjava checker ended, status code " + i);
    }
    return i == 0;
  }


  /**
   * Add the options for the specifications in the option list.
   * @param inputs the argument list
   * @return false if something went wrong.
   */
  private boolean addSpecsOptions(final List<String> inputs) {
    if (!EscjavaUtils.isSpecsInstalled(project)) {
      EscjavaUtils.installDefaultSpecs(project);
    }
    inputs.add("-Specs");
    try {
      final String specLocationFileName = EscjavaUtils.findSpecs();
      inputs.add(specLocationFileName);
    } 
    catch (Exception e1) {
      final String errMsg = 
        EscjavaChecker.COULD_NOT_LOCATE_SPECIFICATIONS_FOR + 
        Options.source.getStringValue();
      Utils.showMessageInUI(null, "Esc/Java", errMsg);
      Log.errorlog(errMsg, e1);
      return false;
    }
    return true;
  }



  private boolean addClasspathOptions(final List<String> inputs) {
    inputs.add("-classpath");
    try {
      String cp = "";
      for (IPackageFragmentRoot f: project.getAllPackageFragmentRoots()) {
        String path = f.getPath().toOSString();
        if (f.getResource() != null) {
          path = f.getResource().getRawLocation().toOSString();
          cp += ":" + path;
        }  
      }
      cp = cp.substring(1);
      inputs.add(cp);
    } 
    catch (JavaModelException e1) {
      inputs.add(Utils.getProjectClassPath(project));
    }
    return true;
  }



  private boolean addSimplifyOptions(final List<String> inputs) {
    // FIXME - can avoid getting simplify if we are not doing any static checking
    
    final String loc = SimplifyEditor.getSimplifyLocation();
  
    if (loc == null) {
      Utils.showMessageInUI(null, "Esc/Java", 
                            "Could not locate a Simplify executable - see error log");
      Log.errorlog("Could not locate a Simplify executable in the plugin: os = " + 
                   System.getProperty("os.name"), null);
      return false;
    }
    inputs.add("-simplify");
    inputs.add(loc);
    if (Log.on) {
      Log.log("Using simplify executable at " + loc);
    }
    // Simplify can get installed without being executable.
    // This is an attempt to fix that, at least on Unix-like platforms
    // This fails benignly on Windows platforms, but they don't need 
    // any changes in permissions
    try {
      if (simplifyloc == null || !loc.equals(simplifyloc)) {
        final Process p = Runtime.getRuntime().exec(
          new String[]{"chmod", "ugo+x", loc});
        p.waitFor();
      }
    } 
    catch (Exception e) { 
      /* skip */
    }
    simplifyloc = loc;
    return true;
  }
}
