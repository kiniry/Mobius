package beetlzplugin.popup.actions;

import ie.ucd.bon.util.StringUtil;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import main.Beetlz;
import main.Beetlz.Status;
import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
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

import beetlzplugin.preferences.PreferenceConstants;
import beetlzplugin.runner.UserSettings;

/**
 * Class for skeleton generation menu item.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @beta-1
 */
public class BeetlzSkeleton implements IObjectActionDelegate {
  /** User option. */
  public boolean useJml;
  /** User option. */
  public boolean useJava;
  /** User option. */
  public boolean printError;
  /** User option. */
  public boolean printWarning;
  /** User option. */
  public boolean verbose;
  /** User option. */
  public boolean pureBon;
  /** User option. */
  public boolean nullCheck;
  /** User option. */
  public boolean useBasics;
  /** User option. */
  public String source;
  /** User option. */
  public String output;
  /** User option. */
  public boolean cancel;

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

  /**
   * Constructor for Action1.
   */
  public BeetlzSkeleton() {
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
  public void run(final IAction action) {
    //Set console , redirected System.out (need for OpenJML errors)
    setConsole();

    //Get options
    final List<String> args = new Vector < String > ();
    final List<String> fileArgs = getFileArguments();

    final boolean cont = getUserOptions(args);
    //Get files
    args.add("-files"); //$NON-NLS-1$
    args.addAll(fileArgs);

    if (cont) {
      try {
        //Now run the Consistency Checker
        final Beetlz beetl =
          new Beetlz(args.toArray(new String[args.size()]), errStream, outStream);

        if (beetl.getStatus() == Status.HELP) {
          err.flush(); out.flush();
        } else if (beetl.getStatus() == Status.PARSING_PROBLEM) {
          err.flush(); out.flush();
          if (err.size() > 0) {
            MessageDialog.openError(
                my_shell, Messages.getString("BeetlzCheck.parsingError"), //$NON-NLS-1$
                err.toString());
          }
          if (Beetlz.getWaitingRecords().size() > 0) {
            MessageDialog.openError(my_shell,
                Messages.getString("BeetlzCheck.errors"), //$NON-NLS-1$
                Beetlz.getWaitingRecords().toString());
          }
          my_console.println(err.toString());
          my_console.println(out.toString());
        } else if (beetl.parsedOK()) {
          beetl.run();
          doOutput(beetl);
        }

        my_project.refreshLocal(IResource.DEPTH_INFINITE, null);
      } catch (final IOException e) {
        MessageDialog.openError(
            my_shell, "Beetlz Plug-in", //$NON-NLS-1$
            Messages.getString("BeetlzCheck.problemsOutput")); //$NON-NLS-1$
      } catch (final CoreException e) {
        MessageDialog.openError(
            my_shell, "Beetlz Plug-in", //$NON-NLS-1$
            Messages.getString("BeetlzCheck.couldNotRefresh")); //$NON-NLS-1$
      }
    }
  }

  /**
   * Get options the user selected on preference page and ask again
   * with gui.
   * @param args arguments list to fill in
   * @return successful and continue?
   */
  private boolean getUserOptions(final List < String > args) {
    IPreferenceStore store = UserSettings.getAppropriatePreferenceStore(my_project);

    final String fileName = store.getString(PreferenceConstants.SPEC_PATH);
    final String userFile = 
      store.getString(PreferenceConstants.USER_SETTING_PATH);
    final String skeleton = store.getString(PreferenceConstants.SKELETON_PATH);
    System.setProperty("java.class.path", //$NON-NLS-1$
        System.getProperty("java.class.path") +  //$NON-NLS-2$
        ";" + fileName); //$NON-NLS-1$
    if (userFile != null && userFile.length() > 0) {
      args.add("-userSettings"); //$NON-NLS-1$
      args.add(userFile);
    }

    //Classpath for openjml
    List<String> cpEntries = Utils.getProjectClassPathEntries(JavaCore.create(my_project));
    String cp = StringUtil.appendWithSeparator(cpEntries, File.pathSeparator);
    args.add("-javajmlcp");
    args.add(cp);

    useJml = store.getBoolean(PreferenceConstants.USE_JML_OPTION);
    useJava = store.getBoolean(PreferenceConstants.USE_JAVA_OPTION);
    printError = store.getBoolean(PreferenceConstants.PRINT_ERROR_OPTION);
    printWarning = store.getBoolean(PreferenceConstants.PRINT_WARNING_OPTION);
    verbose = store.getBoolean(PreferenceConstants.VERBOSE_OPTION);
    pureBon = store.getBoolean(PreferenceConstants.PURE_BON);
    nullCheck = store.getBoolean(PreferenceConstants.NULL_CHECK_OPTION);
    useBasics = store.getBoolean(PreferenceConstants.USE_BASICS_OPTION);
    source = store.getString(PreferenceConstants.SOURCE_OPTION);
    output = "console"; //$NON-NLS-1$
    cancel = false;

    final BeetlzSkeletonGui gui = new BeetlzSkeletonGui(my_shell, SWT.NULL, this);
    gui.open();

    if (cancel) return false;

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

    if (output.equals("onefile")) { //$NON-NLS-1$
      if (skeleton.length() == 0) {
        MessageDialog.openInformation(
            my_shell , Messages.getString("BeetlzSkeleton.skeletonGeneration"), //$NON-NLS-1$
            Messages.getString("BeetlzSkeleton.mustSpeficyDirectory")); //$NON-NLS-1$
        return false;
      } else {
        args.add(Beetlz.SKELETON_OPTION);
        args.add(skeleton);
        args.add(Beetlz.SKELETON_ONE_FILE_OPTION);
      }
    }
    if (output.equals("allfiles")) { //$NON-NLS-1$
      if (skeleton.length() == 0) {
        MessageDialog.openInformation(
            my_shell, Messages.getString("BeetlzSkeleton.skeletonGeneration"), //$NON-NLS-1$
            Messages.getString("BeetlzSkeleton.mustSpeficyDirectory")); //$NON-NLS-1$
        return false;
      } else {
        args.add(Beetlz.SKELETON_OPTION);
        args.add(skeleton);
      }
    } else {
      args.add(Beetlz.SKELETON_OPTION);
    }
    return true;
  }

  /**
   * Print to console.
   * @param c what to print
   */
  private void doOutput(final Beetlz c) {
    my_console.setColor(new Color(null, 255, 0, 0));
    my_console.println(err.toString());
    if (err.size() > 0) {
      MessageDialog.openInformation(
          my_shell, "Beetlz Plug-in", //$NON-NLS-1$
          err.toString());
    }
    my_console.setColor(null);
    my_console.println(out.toString());
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
          } catch (final Exception e){
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
