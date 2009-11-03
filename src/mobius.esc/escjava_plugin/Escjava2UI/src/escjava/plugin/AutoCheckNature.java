/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package escjava.plugin;

import mobius.util.plugin.Utils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;


/**
 * This class implements the nature on which the Escjava builder resides.
 * 
 * @author David R. Cok
 */
public class AutoCheckNature implements IProjectNature {

  /** This is the nature's project. */
  private IProject project;
  
  /** {@inheritDoc} */
  public void configure() throws CoreException {
    Utils.addBuilder(getProject(), EscjavaPlugin.ESCJAVA_AUTOCHECK_BUILDER);
    final IJavaProject jp = JavaCore.create(getProject());
    EscjavaUtils.installDefaultSpecs(jp);
  }
  
  /** {@inheritDoc} */
  public void deconfigure() throws CoreException {
    Utils.removeBuilder(getProject(), EscjavaPlugin.ESCJAVA_AUTOCHECK_BUILDER);
    final IJavaProject jp = JavaCore.create(getProject());
    EscjavaUtils.removeDefaultSpecs(jp);
  }

  /** {@inheritDoc} */
  public IProject getProject() {
    return project;
  }
  
  /** {@inheritDoc} */
  public void setProject(final IProject proj) {
    project = proj;
  }  
}

