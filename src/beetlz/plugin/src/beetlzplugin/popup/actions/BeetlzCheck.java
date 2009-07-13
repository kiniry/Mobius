package beetlzplugin.popup.actions;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
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
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

import utils.SourceLocation;
import beetlzplugin.Activator;
import beetlzplugin.preferences.PreferenceConstants;

/**
 * Class for consistency checking menu item.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @beta-1
 */
public class BeetlzCheck implements IObjectActionDelegate {

  protected static final String JAVA_ERROR_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjavaerrormarker"; //$NON-NLS-1$
  protected static final String JAVA_WARNING_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjavawarningmarker"; //$NON-NLS-1$
  protected static final String JML_ERROR_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjmlerrormarker"; //$NON-NLS-1$
  protected static final String JML_WARNING_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzjmlwarningmarker"; //$NON-NLS-1$
  protected static final String GENERAL_NOTE =
    Activator.PLUGIN_ID + ".beetlzgeneralnotemarker"; //$NON-NLS-1$
  protected static final String NO_LOC_MARKER_ID =
    Activator.PLUGIN_ID + ".beetlzmarker"; //$NON-NLS-1$

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
  /** User option. */
  protected boolean help;
  /** User option. */
  protected boolean cancel;

  /** Selected resources. */
  private ISelection my_selection;
  /** Current eclipse shell. */
  private Shell my_shell;
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
  private Map < String, IResource > pathResourceMap;
  /** The selected project, or at least one of them. */
  private IProject my_project;

  /** The last used specs path, stored so it can be removed from the classpath when changed. */
  private String lastUsedSpecsPath;
  
  /**
   * Constructor for Action1.
   */
  public BeetlzCheck() {
    super();
  }


  /**
   * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
   */
  public void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
    my_shell = targetPart.getSite().getShell();
  }


  /**
   * The actual action happens here.
   * Get necessary settings and selected file information,
   * initialize Beetlz and handle errors.
   * @see IActionDelegate#run(IAction)
   * @param action what called this method
   */
  public final void run(final IAction action) {
    //Set console , redirected System.out (need for OpenJML errors)
    setConsole();
    try {
      IWorkspaceRoot root = my_project.getWorkspace().getRoot();
      root.deleteMarkers(JAVA_ERROR_MARKER_ID, false, IResource.DEPTH_INFINITE);
      root.deleteMarkers(JAVA_WARNING_MARKER_ID, false, IResource.DEPTH_INFINITE);
      root.deleteMarkers(JML_ERROR_MARKER_ID, false, IResource.DEPTH_INFINITE);
      root.deleteMarkers(JML_WARNING_MARKER_ID, false, IResource.DEPTH_INFINITE);
      root.deleteMarkers(NO_LOC_MARKER_ID, false, IResource.DEPTH_INFINITE);
    } catch (final Exception e){}
    //Get options
    final List < String > args = new Vector < String > ();
    final boolean success = getUserOptions(args);

    //Get files
    args.add("-files"); //$NON-NLS-1$
    args.addAll(getFileArguments());

    if (success) {
      try {
        //Now run the Consistency Checker
        final Beetlz beetl = new Beetlz(args.toArray(new String[args.size()]), errStream, outStream);

        if (beetl.getStatus() == Status.HELP) {
          err.flush(); 
          out.flush();
          final BeetlzHelpGui helpGui = new BeetlzHelpGui(my_shell, SWT.NULL);
          helpGui.open();
        } else if (beetl.getStatus() == Status.PARSING_PROBLEM) {
          err.flush(); 
          out.flush();
          if (err.size() > 0) {
//            MessageDialog.openError(
//                my_shell, Messages.getString("BeetlzCheck.parsingError"), //$NON-NLS-1$
//                err.toString());
          }
          if (Beetlz.getWaitingRecords().size() > 0) {
//            MessageDialog.
//            openError(my_shell, Messages.getString("BeetlzCheck.errors"), //$NON-NLS-1$
//                Beetlz.getWaitingRecords().toString());
            my_console.println(Beetlz.getWaitingRecords().toString());
          }
          my_console.println(err.toString());
          my_console.println(out.toString());
        } else if (beetl.parsedOK()) {
          beetl.run();
          doOutput(beetl);
        }

        my_project.refreshLocal(IResource.DEPTH_INFINITE, null);
      } catch (final IOException e) {
//        MessageDialog.openError(
//            my_shell, "Beetlz Plug-in", //$NON-NLS-1$
//            Messages.getString("BeetlzCheck.problemsOutput")); //$NON-NLS-1$
        my_console.println(Messages.getString("BeetlzCheck.problemsOutput"));
      } catch (final CoreException e) {
//        MessageDialog.openError(
//            my_shell, "Beetlz Plug-in", //$NON-NLS-1$
//            Messages.getString("BeetlzCheck.couldNotRefresh")); //$NON-NLS-1$
        my_console.println(Messages.getString("BeetlzCheck.couldNotRefresh"));
      }
    }
  }

  /**
   * Prepend the provided path to the start of the system class path, unless it is already present.
   * @param pathToAdd the path to add to the system class path.
   */
  private void updateClassPath(String pathToAdd) {
    
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
   * Get options the user selected on preference page and ask again
   * with gui.
   * @param args arguments list to fill in
   * @return successful and continue?
   */
  private boolean getUserOptions(final List < String > args) {
    final IPreferenceStore store = Activator.getDefault().getPreferenceStore();
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
    cancel = false;
    help = false;

    final BeetlzGui gui = new BeetlzGui(my_shell, SWT.NULL, this);
    gui.open();

    if (cancel) return false;
    if (help) {
      args.add("-help"); //$NON-NLS-1$
      return true;
    }
    
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

    }


    //my_console.println(System.getProperty("java.class.path"));
    return true;
  }

  /**
   * Print to console and start records converting to markers.
   * @param c
   */
  private void doOutput(final Beetlz c) {
    my_console.println(err.toString());
    if (err.toString().length() > 0) {
//      MessageDialog.openInformation(
//          my_shell, "Beetlz Plug-in", //$NON-NLS-1$
//          err.toString());
      //TODO what should happen here?
    }
    my_console.println(out.toString());

    final SortedSet < CCLogRecord > records = Beetlz.getLogManager().getRecords();
    setMarker(records);


  }

  /**
   * Set marker from log records.
   * @param records records to set
   */
  private void setMarker(final SortedSet < CCLogRecord > records) {
    try {
      for (final CCLogRecord rec : records) {
        final SourceLocation location = rec.getSourceLoc();
        if (location != null) {
          File file = null;
          int line_num = -1;
          if (location.exists()) {
            file = location.getSourceFile();
            line_num = location.getLineNumber();
          }

          //Normal error with location
          if (file != null) {
            final IResource resource = pathResourceMap.get(file.getAbsolutePath());
            if (resource != null) {
              IMarker marker;
              if (rec.getLevel() == CCLevel.JAVA_ERROR) {
                marker = resource.createMarker(JAVA_ERROR_MARKER_ID);
              } else if (rec.getLevel() == CCLevel.JAVA_WARNING) {
                marker = resource.createMarker(JAVA_WARNING_MARKER_ID);
              } else if (rec.getLevel() == CCLevel.JML_ERROR) {
                marker = resource.createMarker(JML_ERROR_MARKER_ID);
              } else if (rec.getLevel() == CCLevel.JML_WARNING) {
                marker = resource.createMarker(JML_WARNING_MARKER_ID);
              } else {
                marker = resource.createMarker(GENERAL_NOTE);
              } //end setting type of marker

              marker.setAttribute(IMarker.MESSAGE,
                  rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
              if (line_num > 0) {
                marker.setAttribute(IMarker.LINE_NUMBER, line_num);
              } else {
                marker.setAttribute(IMarker.LINE_NUMBER, 0);
              } //end setting line numbers
              setSeverity(marker, rec.getLevel());
            }
            //no location file:
          } else {
            IMarker marker;
            if (rec.getLevel() == CCLevel.GENERAL_NOTE) {
              marker = my_project.getWorkspace().getRoot().createMarker(GENERAL_NOTE);
            } else {
              marker = my_project.getWorkspace().getRoot().createMarker(NO_LOC_MARKER_ID);
            }
            marker.setAttribute(IMarker.MESSAGE,
                rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
            setSeverity(marker, rec.getLevel());
          } //end no file
          //no location
        } else {
          IMarker marker;
          if (rec.getLevel() == CCLevel.GENERAL_NOTE) {
            marker = my_project.getWorkspace().getRoot().createMarker(GENERAL_NOTE);
          } else {
            marker = my_project.getWorkspace().getRoot().createMarker(NO_LOC_MARKER_ID);
          }
          marker.setAttribute(IMarker.MESSAGE,
              rec.getMessage().replace("\n", " ")); //$NON-NLS-1$ //$NON-NLS-2$
          setSeverity(marker, rec.getLevel());
        }
      } //end for
    } catch (final Exception e) { }
  }

  /**
   * Set the severity on markers.
   * @param marker marker to set
   * @param level level to deduce severity from
   */
  private void setSeverity(final IMarker marker, final Level level) {
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
   * Get all selected files, recursively searches directories.
   * @return files
   */
  private List < String > getFileArguments() {
    final List < String > args = new Vector < String > ();
    pathResourceMap = new HashMap < String, IResource > ();

    if (!my_selection.isEmpty() && my_selection instanceof IStructuredSelection) {
      final IStructuredSelection sSelection = (IStructuredSelection) my_selection;
      for (final Iterator < ? > iter = sSelection.iterator(); iter.hasNext();) {
        final Object element = iter.next();
        if (element instanceof IResource) {
          final IResource resource = (IResource) element;
          my_project = resource.getProject();
          final ResourceVisitor visitor = new ResourceVisitor();
          try {
            resource.accept(visitor);
          } catch (final Exception e) {
            e.printStackTrace();
          }
          final List < IResource > resources = visitor.getResources();
          if (resources.size() == 0) {
            continue;
          }
          for (final IResource r : resources) {
            final File javaPath = r.getLocation().toFile();
            args.add(javaPath.getAbsolutePath());
            pathResourceMap.put(javaPath.getAbsolutePath(), r);
          }
        }
      }
    }
    return args;
  }

  /**
   * Find the console.
   * @param name name of the console
   * @return current console
   */
  private MessageConsole findConsole(final String name) {
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

  /**
   * @see IActionDelegate#selectionChanged(IAction, ISelection)
   */
  public void selectionChanged(final IAction action, final ISelection selection) {
    my_selection = selection;
  }

}
