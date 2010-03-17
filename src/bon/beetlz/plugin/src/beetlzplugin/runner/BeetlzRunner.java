package beetlzplugin.runner;

import ie.ucd.bon.plugin.util.PluginUtil;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;

import log.CCLevel;
import log.CCLogRecord;
import main.Beetlz;
import main.Beetlz.Status;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

import utils.BeetlzSourceLocation;
import beetlzplugin.Activator;
import beetlzplugin.popup.actions.Messages;
import beetlzplugin.popup.actions.ResourceVisitor;
import beetlzplugin.preferences.PreferenceConstants;
import beetlzplugin.preferences.PreferenceInitializer;

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
  private Map<File,IResource> pathResourceMap;

  /** The last used specs path, stored so it can be removed from the classpath when changed. */
  private static String lastUsedSpecsPath;


  /**
   * Prepend the provided path to the start of the system class path, unless it is already present.
   * @param specsPath the path to add to the system class path.
   */
  private static void updateClassPath(String specsPath) {

    if (lastUsedSpecsPath == null || !lastUsedSpecsPath.equals(specsPath)) {
      //System.out.println("Old classpath: " + System.getProperty("java.class.path"));
      List<String> cpParts = new ArrayList<String>(Arrays.asList(System.getProperty("java.class.path").split(File.pathSeparator)));
      if (lastUsedSpecsPath != null) {
        cpParts.remove(lastUsedSpecsPath);
      }
      List<String> newCPParts = new ArrayList<String>(cpParts.size()+1);
      newCPParts.add(specsPath);
      newCPParts.addAll(cpParts);
      StringBuilder newPath = new StringBuilder(File.pathSeparator);
      for (String path : newCPParts) {
        newPath.append(path);
        //System.out.println("Added: " + path);
        newPath.append(File.pathSeparator);
      }

      System.setProperty("java.class.path",  //$NON-NLS-1$
          newPath.toString());
      //System.out.println("New classpath: " + System.getProperty("java.class.path"));
      lastUsedSpecsPath = specsPath;
    }

  }

  /**
   * Set the severity on markers.
   * @param marker marker to set
   * @param level level to deduce severity from
   */
  private static void setSeverity(final IMarker marker, final Level level) {
    try {
      marker.setAttribute(IMarker.SEVERITY, getSeverity(level));
    } catch (final Exception e) {}
  }

  private static int getSeverity(final Level level) {
    if (level == CCLevel.JAVA_ERROR || level == CCLevel.JML_ERROR) {
      return IMarker.SEVERITY_ERROR;
    } else if (level == CCLevel.JAVA_WARNING || level == CCLevel.JML_WARNING) {
      return IMarker.SEVERITY_WARNING;
    } else {
      return IMarker.SEVERITY_WARNING;
    }
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
    myConsole.activate();
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

    //Redirect System.out, doesnt work for Java Logger for some reason
    err = new ByteArrayOutputStream();
    out = new ByteArrayOutputStream();
    errStream = new PrintStream(err);
    outStream = new PrintStream(out);
    System.setOut(outStream);
    System.setErr(errStream);
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
    UserSettings settings = new UserSettings(project);
    final boolean success = settings.isValid();
    updateClassPath(settings.getSpecsPath());    
    final List<String> args = settings.getUserOptionsAsArgs(); 

    //Classpath for openjml
    List<String> cpEntries = PluginUtil.getProjectClassPathEntries(JavaCore.create(project));
    String setSpecPath = UserSettings.getAppropriatePreferenceStore(project).getString(PreferenceConstants.SPEC_PATH);
    cpEntries.add(setSpecPath);
    String openJMLPath = PreferenceInitializer.attemptToGetJMLSpecsPath();
    if (!openJMLPath.isEmpty() && !openJMLPath.equals(setSpecPath)) {
      cpEntries.add(openJMLPath);
    }    
    String cp = StringUtil.appendWithSeparator(cpEntries, File.pathSeparator);
    args.add("-javajmlcp");
    args.add(cp);

    //Get files
    args.add("-files"); //$NON-NLS-1$
    args.addAll(getFileArgsForProject(project));

    //We have a valid configuration to continue
    if (success) {
      //my_console.println("Beetlz CL args: " + args.toString());
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

    final Collection<CCLogRecord> records = Beetlz.getAllRecords();
    createMarkers(records, project);
  }

  /**
   * Set marker from log records.
   * @param records records to set
   */
  private void createMarkers(final Collection <CCLogRecord> records, final IProject project) {
    try {
      for (final CCLogRecord rec : records) {
        final BeetlzSourceLocation location = rec.getSourceLoc();

        if (location == null || !location.exists() || location.getSourceFile() == null) {
          //No location
          IMarker marker = project.createMarker(getMarkerIDForLevel(rec.getLevel())); 
          marker.setAttribute(IMarker.MESSAGE, rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
          setSeverity(marker, rec.getLevel());
        } else if (location.isJavaFile()) {
          //Normal error with location
          File file = location.getSourceFile();
          final IResource resource = pathResourceMap.get(file);
          if (resource != null) {
            IMarker marker = resource.createMarker(getMarkerIDForLevel(rec.getLevel()));

            marker.setAttribute(IMarker.MESSAGE, rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
            int line_num = location.getLineNumber();
            int charStart = location.getAbsoluteCharPositionStart();
            int charEnd = location.getAbsoluteCharPositionEnd();

            if (line_num != SourceLocation.UNKNOWN) {
              marker.setAttribute(IMarker.LINE_NUMBER, line_num);
            }
            System.out.println("Location:");
            System.out.println(location.toString());
            if (charStart != SourceLocation.UNKNOWN) {
              marker.setAttribute(IMarker.CHAR_START, charStart);
              marker.setAttribute(IMarker.CHAR_END, charEnd);
            }

            setSeverity(marker, rec.getLevel());
          }
        } else {
          //Marker on BON source
          PluginUtil.createMarker(project, getMarkerIDForLevel(rec.getLevel()), 
              location, pathResourceMap, rec.getMessage().replace("\n", " "), getSeverity(rec.getLevel()));
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
    final ResourceVisitor visitor = new ResourceVisitor();
    try {
      project.accept(visitor);
    } catch (final Exception e) {
      e.printStackTrace();
    }
    final List<IResource> resources = visitor.getResources();

    pathResourceMap = PluginUtil.getResourceMap(resources);
    for (final File f : pathResourceMap.keySet()) {
      args.add(f.getAbsolutePath());
    }
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
