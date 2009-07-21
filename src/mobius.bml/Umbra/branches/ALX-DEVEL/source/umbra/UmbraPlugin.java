/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra;

import java.io.PrintStream;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The main plugin class to be used in the desktop.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class UmbraPlugin extends AbstractUIPlugin {

  /**
   * The standard logging facility for the plugin.
   */
  public static final PrintStream LOG = System.out;

  /**
   * The shared instance of the plugin.
   */
  private static UmbraPlugin plugin;

  /**
   * The constructor which shares the instance.
   */
  public UmbraPlugin() {
    plugin = this;
  }

  /**
   * This method is called upon plug-in activation.
   *
   * @param a_context the context from which the bundle for this plug-in is
   * extracted
   * @throws Exception if this method fails to shut down this plug-in
   */
  public final void start(final BundleContext a_context) throws Exception {
    super.start(a_context);
  }

  /**
   * This method is called when the plug-in is stopped.
   *
   * @param a_context the context from which the bundle for this plug-in is
   * extracted
   * @throws Exception if this method fails to shut down this plug-in
   */
  public final void stop(final BundleContext a_context) throws Exception {
    super.stop(a_context);
    plugin = null;
  }

  /**
   * Returns the shared instance.
   *
   * @return the only instance of the Umbra plugin in the system.
   */
  public static UmbraPlugin getDefault() {
    return plugin;
  }

  /**
   * Returns an image descriptor for the image file at the given
   * plug-in relative path.
   *
   * @param a_path the path for the image
   * @return the image descriptor
   */
  public static ImageDescriptor getImageDescriptor(final String a_path) {
    return AbstractUIPlugin.imageDescriptorFromPlugin("umbra", a_path);
  }

  /**
   * This method prints out the string to the current logging facility.
   *
   * @param a_string the string to print to the log
   */
  public static void messagelog(final String a_string) {
    LOG.println(a_string);
  }
}
