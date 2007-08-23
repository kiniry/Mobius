/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package escjava.plugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;

import pluginlib.Utils;

/**
 * This class implements the nature on which the Escjava builder resides.
 * 
 * @author David R. Cok
 */
public class AutoCheckNature implements IProjectNature {
	
	/**
	 * This is the nature's project.
	 */
	private IProject project;
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IProjectNature#configure()
	 */
	public void configure() throws CoreException {

		Utils.addBuilder(getProject(),EscjavaPlugin.ESCJAVA_AUTOCHECK_BUILDER);
		IJavaProject jp = JavaCore.create(getProject());
		EscjavaUtils.installDefaultSpecs(jp);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IProjectNature#deconfigure()
	 */
	public void deconfigure() throws CoreException {
		Utils.removeBuilder(getProject(),EscjavaPlugin.ESCJAVA_AUTOCHECK_BUILDER);
	}


		
	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IProjectNature#getProject()
	 */
	public IProject getProject() {
		return project;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IProjectNature#setProject(org.eclipse.core.resources.IProject)
	 */
	public void setProject(IProject project) {
		this.project = project;
	}
	
}

