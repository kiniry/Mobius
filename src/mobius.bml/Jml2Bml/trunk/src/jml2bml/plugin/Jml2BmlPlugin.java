/*
 * @title "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright "(c)2008-01-06 University of Warsaw"
 * @license "All rights reserved. This program and the accompanying materials
 * are made available under the terms of the LGPL licence see LICENCE.txt file"
 */
package jml2bml.plugin;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;

import jml2bml.Main;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.exceptions.NotTranslatedException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.osgi.util.ManifestElement;
import org.osgi.framework.BundleContext;
import org.osgi.framework.BundleException;
import org.osgi.framework.Constants;

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
  
  private String getPluginClasspath() throws BundleException, IOException{
    String pluginLocation = FileLocator.toFileURL(getBundle().getEntry("/")).getPath();
    
    String requires = (String) getBundle().getHeaders().get(Constants.BUNDLE_CLASSPATH);
    StringBuffer result = new StringBuffer();
    for(ManifestElement element: ManifestElement.parseHeader(Constants.BUNDLE_CLASSPATH, requires)){
      result.append(java.io.File.pathSeparator+pluginLocation+element.getValue());
    }
    return result.toString();
  }
  
  private String getOutputLocation(final IJavaProject project) throws JavaModelException {
    IWorkspaceRoot wr = ResourcesPlugin.getWorkspace().getRoot();
    IPath oloc = project.getOutputLocation();
    IPath proot = project.getPath();
    if (!oloc.equals(proot)) 
      return wr.getFolder(oloc).getLocation().toOSString();
    else
      return project.getResource().getLocation().toOSString();
  }
  
  private String getProjectClassPath(final IJavaProject project) throws JavaModelException{
    IWorkspaceRoot wr = ResourcesPlugin.getWorkspace().getRoot();
    StringBuffer result = new StringBuffer();
    result.append(getOutputLocation(project));
    
    for (IClasspathEntry entry: project.getRawClasspath()){
      switch (entry.getEntryKind()) {
        case IClasspathEntry.CPE_SOURCE:
          if (entry.getOutputLocation() != null)
            result.append(java.io.File.pathSeparator+entry.getOutputLocation());          
          break;
        case IClasspathEntry.CPE_LIBRARY:
          result.append(java.io.File.pathSeparator+wr.getFolder(entry.getPath()).getLocation().toOSString());
        default:
//          System.out.println(entry.getPath());
          break;
      }
    }
    
    return result.toString();
  }

  public void compile(final IFile a_jfile, final IJavaProject project, OutputStream out)
      throws ClassNotFoundException, ReadAttributeException, IOException, jml2bml.plugin.NotTranslatedException, JavaModelException{
    PrintWriter writer = new PrintWriter(out);
    final String outputLocation = getOutputLocation(project);
    
    String bundleClassPath;
    try {
      bundleClassPath = getPluginClasspath();
    } catch (BundleException e) {
      e.printStackTrace();
      bundleClassPath = "";
    }
    
//    writer.println("BUNDLE CLASSPATH:"+bundleClassPath);
    
    String projectClassPath;
    try {
      projectClassPath = getProjectClassPath(project);
    } catch (JavaModelException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
      projectClassPath = "";
    }
    
//    writer.println("PROJECT CLASSPATH:"+projectClassPath);
    String oldPath = System.getProperty("java.class.path");
    String oldCPath = System.getProperty("env.class.path");
    try {
      // TODO: hack to use internal jmlspecs!!
      System.setProperty("java.class.path", bundleClassPath);
      writer.println("java.class.path = " + System.getProperty("java.class.path"));
      System.setProperty("env.class.path", projectClassPath+java.io.File.pathSeparator+bundleClassPath);
      writer.println("env.class.path = "+ System.getProperty("env.class.path"));
      new Main().compile(a_jfile.getLocation().toOSString(), outputLocation, outputLocation, projectClassPath, writer);
    } catch (NotTranslatedException e2) {
      throw new jml2bml.plugin.NotTranslatedException(e2);
    } catch (Jml2BmlException e2) {
      throw new jml2bml.plugin.NotTranslatedException(e2);      
    }  
    System.setProperty("java.class.path", oldPath);
    if (oldCPath!=null)
      System.setProperty("env.class.path", oldCPath);
    else
      System.clearProperty("env.class.path");

  }
}
