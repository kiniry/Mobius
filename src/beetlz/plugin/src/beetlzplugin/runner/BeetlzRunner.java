package beetlzplugin.runner;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.Vector;
import java.util.logging.Level;

import log.CCLevel;
import log.CCLogRecord;
import main.Beetlz;
import main.Beetlz.Status;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import utils.SourceLocation;
import beetlzplugin.Activator;
import beetlzplugin.popup.actions.Messages;
import beetlzplugin.popup.actions.ResourceVisitor;
import beetlzplugin.preferences.PreferenceConstants;

public class BeetlzRunner {

  protected static final String JAVA_ERROR_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjavaerrormarker"; //$NON-NLS-1$
  protected static final String JAVA_WARNING_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjavawarningmarker"; //$NON-NLS-1$
  protected static final String JML_ERROR_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjmlerrormarker"; //$NON-NLS-1$
  protected static final String JML_WARNING_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjmlwarningmarker"; //$NON-NLS-1$
  protected static final String GENERAL_NOTE_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzgeneralnotemarker"; //$NON-NLS-1$
  protected static final String NO_LOC_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzmarker"; //$NON-NLS-1$

  /** Console. */
  private MessageConsoleStream my_console;
  /** Output stream for errors. */
  private ByteArrayOutputStream err;
  /** Output stream. */
  private ByteArrayOutputStream out;
  /** Output stream for errors. */
  private PrintStream errStream;
  /** Output stream. */
  private PrintStream outStream;

  /** Remember which resource has which name. */
  private Map<String,IResource> pathResourceMap;

  /** The last used specs path, stored so it can be removed from the classpath when changed. */
  private static String lastUsedSpecsPath;


  /**
   * Prepend the provided path to the start of the system class path, unless it is already present.
   * @param pathToAdd the path to add to the system class path.
   */
  private static void updateClassPath(String pathToAdd) {

    if (lastUsedSpecsPath == null || !lastUsedSpecsPath.equals(pathToAdd)) {
      System.out.println("Old classpath: " + System.getProperty("java.class.path"));
      List<String> cpParts = new ArrayList<String>(Arrays.asList(System.getProperty("java.class.path").split(File.pathSeparator)));
      if (lastUsedSpecsPath != null) {
        cpParts.remove(lastUsedSpecsPath);
      }
      List<String> newCPParts = new ArrayList<String>(cpParts.size()+1);
      newCPParts.add(pathToAdd);
      newCPParts.addAll(cpParts);
      StringBuilder newPath = new StringBuilder(File.pathSeparator);
      for (String path : newCPParts) {
        newPath.append(path);
        System.out.println("Added: " + path);
        newPath.append(File.pathSeparator);
      }

      System.setProperty("java.class.path",  //$NON-NLS-1$
          newPath.toString());
      System.out.println("New classpath: " + System.getProperty("java.class.path"));
      lastUsedSpecsPath = pathToAdd;
    }

  }

  /**
   * Set the severity on markers.
   * @param marker marker to set
   * @param level level to deduce severity from
   */
  private static void setSeverity(final IMarker marker, final Level level) {
    try {
      if (level == CCLevel.JAVA_ERROR ||
          level == CCLevel.JML_ERROR) {
        marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
      } else if (level == CCLevel.JAVA_WARNING ||
          level == CCLevel.JML_WARNING) {
        marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
      } else {
        marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
      }
    } catch (final Exception e) {}
  }

  /**
   * Find the console.
   * @param name name of the console
   * @return current console
   */
  private static MessageConsole findConsole(final String name) {
    final ConsolePlugin plugin = ConsolePlugin.getDefault();
    final IConsoleManager conMan = plugin.getConsoleManager();
    final IConsole[] existing = conMan.getConsoles();
    for (int i = 0; i < existing.length; i++)
      if (name.equals(existing[i].getName()))
        return (MessageConsole) existing[i];
    //no console found, so create a new one
    final MessageConsole myConsole = new MessageConsole(name, null);
    conMan.addConsoles(new IConsole[]{myConsole});
    return myConsole;
  }

  /**
   * Configure the console.
   */
  private void setConsole() {
    //Set up console
    final MessageConsole myConsole = findConsole(IConsoleConstants.ID_CONSOLE_VIEW);
    my_console = myConsole.newMessageStream();

    //Clear console:
    myConsole.clearConsole();
    myConsole.activate();

    //Redirect System.out, doesnt work for Java Logger for some reason
    err = new ByteArrayOutputStream();
    out = new ByteArrayOutputStream();
    errStream = new PrintStream(err);
    outStream = new PrintStream(out);
    System.setOut(outStream);
    System.setErr(errStream);
  }

  /** User option. */
  protected boolean useJml;
  /** User option. */
  protected boolean useJava;
  /** User option. */
  protected boolean printError;
  /** User option. */
  protected boolean printWarning;
  /** User option. */
  protected boolean verbose;
  /** User option. */
  protected boolean pureBon;
  /** User option. */
  protected boolean nullCheck;
  /** User option. */
  protected boolean useBasics;
  /** User option. */
  protected String source;

  private static IPreferenceStore getPreferenceStore(final IProject project) {
    ProjectScope projectScope = new ProjectScope(project);
    InstanceScope instanceScope = new InstanceScope();
    ScopedPreferenceStore store = new ScopedPreferenceStore(new ProjectScope(project), Activator.PLUGIN_ID);
    store.setSearchContexts(new IScopeContext[] { projectScope, instanceScope });
    
    return store;
  }
  
  /**
   * Get options the user selected on preference page and ask again
   * with gui.
   * @param args arguments list to fill in
   * @return successful and continue?
   */
  private boolean getUserOptions(final List <String> args, final IProject project) {
    final IPreferenceStore store = getPreferenceStore(project);
    final String fileName = store.getString(PreferenceConstants.SPEC_PATH);
    final String userFile = store.getString(PreferenceConstants.USER_SETTING_PATH);

    updateClassPath(fileName);

    if (userFile != null && userFile.length() > 0) {
      args.add(Beetlz.USERSET_OPTION); //$NON-NLS-1$
      args.add(userFile);
    }

    useJml = store.getBoolean(PreferenceConstants.USE_JML_OPTION);
    useJava = store.getBoolean(PreferenceConstants.USE_JAVA_OPTION);
    printError = store.getBoolean(PreferenceConstants.PRINT_ERROR_OPTION);
    printWarning = store.getBoolean(PreferenceConstants.PRINT_WARNING_OPTION);
    verbose = store.getBoolean(PreferenceConstants.VERBOSE_OPTION);
    pureBon = store.getBoolean(PreferenceConstants.PURE_BON);
    nullCheck = store.getBoolean(PreferenceConstants.NULL_CHECK_OPTION);
    useBasics = store.getBoolean(PreferenceConstants.USE_BASICS_OPTION);
    source = store.getString(PreferenceConstants.SOURCE_OPTION);

    args.add(Beetlz.SPECS_OPTION);
    args.add(fileName);

    if (!useJml) args.add(Beetlz.NO_JML_OPTION);
    if (!useJava) args.add(Beetlz.NO_JAVA_OPTION);
    if (!printError) args.add(Beetlz.NO_ERROR_OPTION);
    if (!printWarning) args.add(Beetlz.NO_WARNING_OPTION);
    if (verbose) args.add(Beetlz.VERBOSE_OPTION);
    if (pureBon) args.add(Beetlz.PUREBON_OPTION);
    if (!nullCheck) args.add(Beetlz.NON_NULL_OPTION);
    if (!useBasics) args.add(Beetlz.NO_BASICS_OPTION);
    if (source.equals("java")) { //$NON-NLS-1$
      args.add(Beetlz.SOURCE_OPTION);
      args.add("java"); //$NON-NLS-1$
    } else if (source.equals("bon")) { //$NON-NLS-1$
      args.add(Beetlz.SOURCE_OPTION);
      args.add("bon"); //$NON-NLS-1$
    } else if (source.equals("both")) {
      args.add(Beetlz.SOURCE_OPTION);
      args.add("both"); //$NON-NLS-1$
    }

    //my_console.println(System.getProperty("java.class.path"));
    return true;
  }

  /**
   * The actual action happens here.
   * Get necessary settings and selected file information,
   * initialize Beetlz and handle errors.
   * @see IActionDelegate#run(IAction)
   * @param action the action that called this method
   */
  public final void runChecker(final IProject project) {
    //Set console , redirected System.out (need for OpenJML errors)
    setConsole();

    //Remove old markers for project
    try {
      removeAllBeetlzMarkers(project);
    } catch (final Exception e) { }

    //Get options
    final List < String > args = new Vector < String > ();
    final boolean success = getUserOptions(args, project);

    //Get files
    args.add("-files"); //$NON-NLS-1$
    args.addAll(getFileArgsForProject(project));

    //We have a valid configuration to continue
    if (success) {
      try {
        //Now run the Consistency Checker
        final Beetlz beetl = new Beetlz(args.toArray(new String[args.size()]), errStream, outStream);

        if (beetl.getStatus() == Status.PARSING_PROBLEM) {
          err.flush(); 
          out.flush();

          if (Beetlz.getWaitingRecords().size() > 0) {
            my_console.println(Beetlz.getWaitingRecords().toString());
          }
          my_console.println(err.toString());
          my_console.println(out.toString());

        } else if (beetl.parsedOK()) {
          beetl.run();
          doOutput(beetl, project);
        }

        project.refreshLocal(IResource.DEPTH_INFINITE, null);
      } catch (final IOException e) {
        my_console.println(Messages.getString("BeetlzCheck.problemsOutput"));
      } catch (final CoreException e) {
        my_console.println(Messages.getString("BeetlzCheck.couldNotRefresh"));
      }
    }
  }

  /**
   * Print to console and start records converting to markers.
   * @param c
   */
  private void doOutput(final Beetlz c, final IProject project) {
    my_console.println(err.toString());
    if (err.toString().length() > 0) {
      //TODO what should happen here? It used to be a popup
    }
    my_console.println(out.toString());

    final SortedSet<CCLogRecord> records = Beetlz.getLogManager().getRecords();
    createMarkers(records, project);
  }

  /**
   * Set marker from log records.
   * @param records records to set
   */
  private void createMarkers(final SortedSet <CCLogRecord> records, final IProject project) {
    try {
      for (final CCLogRecord rec : records) {
        final SourceLocation location = rec.getSourceLoc();
        
        if (location != null && location.exists() && location.getSourceFile() != null) {
          //Normal error with location
          File file = location.getSourceFile();
          int line_num = location.getLineNumber();

            final IResource resource = pathResourceMap.get(file.getAbsolutePath());
            if (resource != null) {
              IMarker marker = resource.createMarker(getMarkerIDForLevel(rec.getLevel()));

              marker.setAttribute(IMarker.MESSAGE,
                  rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
              if (line_num > 0) {
                marker.setAttribute(IMarker.LINE_NUMBER, line_num);
              } else {
                marker.setAttribute(IMarker.LINE_NUMBER, 0);
              } //end setting line numbers
              setSeverity(marker, rec.getLevel());
            }

        } else {
          //No location
          IMarker marker = project.createMarker(getMarkerIDForLevel(rec.getLevel())); 
          
          marker.setAttribute(IMarker.MESSAGE,
              rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
          setSeverity(marker, rec.getLevel());
        }
      } //end for
    } catch (final Exception e) { }
  }
  
  private String getMarkerIDForLevel(Level level) {
    if (level == CCLevel.JAVA_ERROR) {
      return JAVA_ERROR_MARKER_ID;
    } else if (level == CCLevel.JAVA_WARNING) {
      return JAVA_WARNING_MARKER_ID;
    } else if (level == CCLevel.JML_ERROR) {
      return JML_ERROR_MARKER_ID;
    } else if (level == CCLevel.JML_WARNING) {
      return JML_WARNING_MARKER_ID;
    } else {
      return GENERAL_NOTE_MARKER_ID;
    }
      
  }

  private List<String> getFileArgsForProject(final IProject project) {
    List<String> args = new ArrayList<String>();
    pathResourceMap = new HashMap < String,IResource> ();
    final ResourceVisitor visitor = new ResourceVisitor();
    try {
      project.accept(visitor);
    } catch (final Exception e) {
      e.printStackTrace();
    }
    final List<IResource> resources = visitor.getResources();
    for (final IResource r : resources) {
      final File javaPath = r.getLocation().toFile();
      args.add(javaPath.getAbsolutePath());
      pathResourceMap.put(javaPath.getAbsolutePath(), r);
    }
    System.out.println("Files: " + args);
    return args;
  }

  public static void removeAllBeetlzMarkers(IResource resource) throws CoreException {
    resource.deleteMarkers(JAVA_ERROR_MARKER_ID, false, IResource.DEPTH_INFINITE);
    resource.deleteMarkers(JAVA_WARNING_MARKER_ID, false, IResource.DEPTH_INFINITE);
    resource.deleteMarkers(JML_ERROR_MARKER_ID, false, IResource.DEPTH_INFINITE);
    resource.deleteMarkers(JML_WARNING_MARKER_ID, false, IResource.DEPTH_INFINITE);
    resource.deleteMarkers(GENERAL_NOTE_MARKER_ID, false, IResource.DEPTH_INFINITE);
    resource.deleteMarkers(NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);
  }
}
