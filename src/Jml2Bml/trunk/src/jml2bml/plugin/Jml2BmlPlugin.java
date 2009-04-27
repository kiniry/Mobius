/*
 * @title "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright "(c)2008-01-06 University of Warsaw"
 * @license "All rights reserved. This program and the accompanying materials
 * are made available under the terms of the LGPL licence see LICENCE.txt file"
 */
package jml2bml.plugin;

import java.io.IOException;
import java.io.PrintStream;

import jml2bml.Main;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.exceptions.NotTranslatedException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.osgi.baseadaptor.loader.ClasspathEntry;
import org.eclipse.osgi.internal.baseadaptor.DefaultClassLoader;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;

import annot.io.ReadAttributeException;

public class Jml2BmlPlugin extends Plugin {

  /**
   * The standard logging facility for the plugin.
   */
  public static final PrintStream LOG = System.out;

  /**
   * The shared instance of the plugin.
   */
  private static Jml2BmlPlugin plugin;

  /**
   * The constructor which shares the instance.
   */
  public Jml2BmlPlugin() {
    plugin = this;
  }

  /**
   * This method is called upon plug-in activation.
   *
   * @param a_context the context from which the bundle for this plug-in is
   * extracted
   * @throws Exception if this method fails to shut down this plug-in
   */
  @Override
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
  @Override
  public final void stop(final BundleContext a_context) throws Exception {
    super.stop(a_context);
    plugin = null;
  }

  /**
   * Returns the shared instance.
   *
   * @return the only instance of the Umbra plugin in the system.
   */
  public static Jml2BmlPlugin getDefault() {
    return plugin;
  }

  /**
   * This method prints out the string to the current logging facility.
   *
   * @param a_string the string to print to the log
   */
  public static void messagelog(final String a_string) {
    LOG.println(a_string);
  }

  public void compile(final IFile a_jfile, final IFile a_bfile)
      throws ClassNotFoundException, ReadAttributeException, IOException, jml2bml.plugin.NotTranslatedException{
    ClassLoader applicationClassLoader = this.getClass().getClassLoader();
    if (applicationClassLoader == null) {
      applicationClassLoader = ClassLoader.getSystemClassLoader();
    }
    ClasspathEntry[] cp = ((DefaultClassLoader) applicationClassLoader)
        .getClasspathManager().getHostClasspathEntries();
    String bundleClassPath = "";
    for (ClasspathEntry i : cp) {
      bundleClassPath += java.io.File.pathSeparator +
                         i.getBundleFile().toString();
    }
    System.out.println(bundleClassPath);

    String bname = a_bfile.getName();
    final IPath path = a_bfile.getLocation();
    bname = bname.substring(0, bname.lastIndexOf("."));
    final String bpath = path.removeLastSegments(1).toOSString();
    final String sourceFile = a_jfile.getLocation().toOSString();
    String oldPath = System.getProperty("java.class.path");
    try {
      // TODO: hack to use internal jmlspecs!!
      System.setProperty("java.class.path", bundleClassPath);
      new Main().compile(sourceFile, new ClassFileLocation(bpath, bname), path.toOSString());
    } catch (NotTranslatedException e2) {
      throw new jml2bml.plugin.NotTranslatedException(e2);
    }
    System.setProperty("java.class.path", oldPath);

  }
}
