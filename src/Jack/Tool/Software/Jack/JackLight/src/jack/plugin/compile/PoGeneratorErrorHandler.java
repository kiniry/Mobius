//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: PoGeneratorErrorHandler.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.compile;

import jack.plugin.Generator;
import jack.plugin.JackPlugin;
import jack.util.Logger;

import java.io.File;

import jml2b.exceptions.ErrorHandler;
import jml2b.structure.java.JmlFile;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;

/**
 * Error handler that adds markers for errors instead of just printing errors
 * to stderr.
 * 
 * @author A. Requet, L. Burdy
 */
public class PoGeneratorErrorHandler extends ErrorHandler {
	/** 
	 * The project containing the files that are parsed.
	 * It is used as a last resort for displaying markers, when
	 * the file could not be found.
	 */
	IProject project;
	
	public PoGeneratorErrorHandler(IProject prj)
	{
		project = prj;
	}
	
	/**
	 * Return the path of children relative to root.
	 * 
	 * Return null if children is not located in a subdirectory of root.
	 */
	public static String getRelativeFile(File root, File children)
	{
		String absolute_root, absolute_children;
		
		absolute_root = root.getAbsolutePath();
		absolute_children = children.getAbsolutePath();
		// removes the common part of the file.
		if(absolute_children.startsWith(absolute_root)) {
			return absolute_children.substring(absolute_root.length());
		} else {
			return null;
		}
	}
	
	/** 
	 * Return the eclipse resource corresponding to the given JmlFile.
	 * 
	 * return null if no matching resource could be found.
	 */
	static IResource getResource(JmlFile jml_file)
	{
		File f = jml_file.fileName.getFile();
		if (f == null)
			return null;
		IWorkspaceRoot root = JackPlugin.getWorkspace().getRoot();
		IProject [] projects = root.getProjects();
		
		for(int i=0; i<projects.length; ++i) {
			File project_file = projects[i].getLocation().toFile();
			String relative_path = getRelativeFile(project_file, f);
		
			if(relative_path != null) {
				return projects[i].getFile(relative_path);
			}
		}
		return null;
	}
		
	/**
	 * Implementation of handleError using markers.
	 * <p>
	 * @see jml2b.exceptions.ErrorHandler#handleError(JmlFile, int, int, String)
	 */
	protected void handleError(JmlFile f, int line, int column, String description) {
		createMarker(IMarker.SEVERITY_ERROR, f, line, description);
	}

	/**
	 * implementation of handleWarning that adds a marker for the resource 
	 * corresponding to the given jml file.
	 * <p>
	 * @see jml2b.exceptions.ErrorHandler#handleWarning(JmlFile, int, int, String)
	 */
	protected void handleWarning(JmlFile f, int line, int column, String description) {
		createMarker(IMarker.SEVERITY_WARNING, f, line, description);
	}

	/**
	 * Creates a marker on the given file.
	 * 
	 * @param severity severity of the marker. Can be IMarker.SEVERITY_WARNING or
	 *         IMarker.SEVERITY_ERROR.
	 * @param f the JmlFile on which the marker should be set.
	 * @param line the line where the problem occurs (-1 means unknown).
	 * @param description the description of the problem.
	 */
	private void createMarker(int severity, JmlFile f, int line, String description)
	{
		IResource resource = null;
		
		if(f != null) {
			// get the resource associated to the JmlFile
			resource = (IResource)f.getData(Generator.ECLIPSE_RESOURCE_KEY);

			if(resource == null) {
				resource = getResource(f);
				
				if(resource != null) {
					// if the resource has been found, store it for later retrieval
					f.storeData(Generator.ECLIPSE_RESOURCE_KEY, resource);
				}
			}
		}
		
		if(resource == null) {
			resource = project/*.getResource()*/;
			if(f != null) {
				description += " (File : " + f.fileName + ")";
			}
		}
		
		try {
			// create the marker
			IMarker marker = resource.createMarker(Generator.PROBLEM_MARKER_TYPE);
			if(marker == null) {
				Logger.err.println("Warning: could not create marker");
				return;
			}

			// fill the marker information
			marker.setAttribute(IMarker.MESSAGE, description);
			if(line >=0) {
				marker.setAttribute(IMarker.LINE_NUMBER, line);
			}
			marker.setAttribute(IMarker.SEVERITY, severity);
		} catch(CoreException e) {
			// should never happen
			Logger.err.println("Warning: catched : " + e.toString());
		}		
	}
}
