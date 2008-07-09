package mobius.directVCGen.ui.poview;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Activator extends AbstractUIPlugin implements IImagesConstants {

  /** The plug-in ID. */
  public static final String PLUGIN_ID = "MobiusDirectVCGenUI";

  /** The shared instance. */
  private static Activator plugin;
  /** the color red. */
  private static final RGB RED = new RGB(255, 0, 0);
  /** the color blue. */
  private static final RGB BLUE = new RGB(0, 0, 255);
  /** the color purple. */
  private static final RGB PURPLE = new RGB(255, 0, 255);

  /** the output console, used to write information to the user. */
  private IOConsole fConsole;
  /** the display dependent red color. */
  private Color fRed;
  /** the display dependent blue color. */
  private Color fBlue;
  /** the display dependent purple color. */
  private Color fPurple;
  
  
  /**
   * The constructor.
   */
  public Activator() {
    plugin = this;
  }

  /** {@inheritDoc} */
  public void start(final BundleContext context) throws Exception {
    super.start(context);
    fConsole = new IOConsole("Mobius DirectVCGen Console", Utils.descTool);
    fConsole.activate();
    ConsolePlugin.getDefault().getConsoleManager().addConsoles(new IConsole[]{fConsole});
    final Display display = PlatformUI.getWorkbench().getDisplay();
    fRed = new Color(display, RED);
    fBlue = new Color(display, BLUE);
    fPurple = new Color(display, PURPLE);
  }

  /** {@inheritDoc} */
  public void stop(final BundleContext context) throws Exception {
    //plugin = null;
    fRed.dispose();
    fBlue.dispose();
    fPurple.dispose();
    super.stop(context);
    
  }

  /**
   * Returns the shared instance.
   *
   * @return the shared instance
   */
  public static Activator getDefault() {
    return plugin;
  }
  
  /**
   * Returns the plugin console.
   * @return a valid console
   */
  public IOConsole getConsole() {
    return fConsole;
  }
  
  /**
   * Returns the color red.
   * @return not null
   */
  public Color getRed() {
    return fRed;
  }
  
  /**
   * Returns the color blue.
   * @return not null
   */
  public Color getBlue() {
    return fBlue;
  }
  
  /**
   * Returns the color purple.
   * @return not null
   */
  public Color getPurple() {
    return fPurple;
  }
}
