/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package escjava.plugin;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ui.internal.ide.IMarkerImageProvider;

import pluginlib.Log;
import pluginlib.Utils;

/**
 * This class manages a new type of marker for Esc/Java2 warnings.
 * 
 * @author David R. Cok
 */
public class EscjavaMarker implements IEscjavaListener {
	
	/** 
	 * The id that is also used in plugin.xml.
	 */
	final static public String ESCJAVA_MARKER_ID =
		EscjavaPlugin.PLUGINID + ".escjavaWarningMarker";
	
	/** The id of the marker property that holds the 'associated declaration' information. */
	final static public String EXTRA_INFO = "declarationInfo";
	
	/**
	 * A callback method called when a marker should be created.
	 * @param resource The resource in which the error occured
	 * @param file The file in which the error occured
	 * @param lineNumber The line number where the error happened
	 * @param offset The character position (0-based) from the beginning of the file where the error begins
	 * @param length The number of characters to highlight
	 * @param errorMessage A message explaining the type of error
	 * @param severity The severity of the error (using one of the error severity constants defined in this class)
	 */
	public void escjavaFailed(
			IResource resource,
			String file,
			int lineNumber,
			int offset,
			int length,
			String errorMessage,
			final int severity) {

		IResource res = null;
		if (file == null) {
			res = resource;
		} else {
			
			// FIXME - this works as long as the filename coming in
			// is a totally absolute file-system path name
			// Is it ever something else?  Can we tell and adjust using 
			// java system calls?
			// DOes it work when the file is linked? - e.g. specs files
			IPath filePath = new Path(file);
			IFile ffile = Utils.getRoot().getFileForLocation(filePath);
			res = ffile;
			if (res == null) {
				// It is likely that filePath is an absolute path to
				// a linked resource
				IResource s = Utils.mapBack(JavaCore.create(resource.getProject()),file,false);
				res = s != null ? s : resource;
			}
		}
		
		if (Log.on) {
			Log.log("MARKER " + file + " " + lineNumber + " " +
					errorMessage);
		}
		
		final int finalLineNumber = lineNumber;
		final int finalOffset = offset;
		final int finalLength = length;
		final String finalErrorMessage = errorMessage;
		
		try {
			final IResource r = res;
			// Eclipse recommends that things that modify the resources
			// in a workspace be performed in a IWorkspaceRunnable
			IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
				public void run(IProgressMonitor monitor) throws CoreException {
					IMarker marker = r.createMarker(ESCJAVA_MARKER_ID);
					setMarkerAttributes(marker, finalLineNumber, finalOffset, finalLength, finalErrorMessage, severity);
				}
			};
			r.getWorkspace().run(runnable, null);
		} catch (CoreException e) {
			Log.errorlog("Unexpected exception while creating a Marker: ",e);
		}
	}
	
	/** A cache of the most recently produced marker, so that associated info
	 *  coming in subsequent jmlFailed calls can be associated with the correct marker.
	 */
	// FIXME - another reason this is not thread-safe
	private static IMarker mostRecentMarker = null;
	
	/**
	 * Sets the attributes of a marker.
	 * @param marker The marker whose attributes are to be set
	 * @param finalLineNumber The line to mark, beginning with 1; use 0 if no line should be marked.
	 * @param finalOffset The starting 0-based character number within the file to mark
	 * @param finalLength The length in characters of the error location.
	 * @param finalErrorMessage The message conveying relevant information
	 * @param severity The severity (values from IEscjavaListener).
	 * @throws JavaModelException
	 * @throws CoreException
	 */
	private void setMarkerAttributes(IMarker marker, 
			int finalLineNumber, int finalOffset,
			int finalLength,
			String finalErrorMessage, int severity)
	throws JavaModelException, CoreException {
		mostRecentMarker = marker;
		if (finalLineNumber >= 1) {
			marker.setAttribute(IMarker.LINE_NUMBER, finalLineNumber);
		}
		if (finalOffset >= 0) {
			marker.setAttribute(IMarker.CHAR_START, finalOffset); 
			marker.setAttribute(IMarker.CHAR_END, finalOffset+(finalLength>0?finalLength:2));
		}
			// Note - it appears that CHAR_START is measured from the beginning of the
			// file and overrides the line number

		marker.setAttribute(IMarker.SEVERITY,
				severity == ERROR ? IMarker.SEVERITY_ERROR :
					severity == WARNING ? IMarker.SEVERITY_WARNING:
									IMarker.SEVERITY_INFO);
		marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
	}

	/**
	 * Adds extra information to the most recently 
	 * created marker
	 * 
	 * @param s The additional information to be added
	 * @throws CoreException
	 */
	//@ requires mostRecentMarkerInfo != null;
	static public void addMarkerInfo(String s) throws CoreException {
		if (Log.on) Log.log("Adding extra marker info: " + s);
		Object o = mostRecentMarker.getAttribute(EXTRA_INFO);
		String a;
		if (o == null) {
			a = s;
		} else {
			a = (String)o + "; " + s;
		}
		mostRecentMarker.setAttribute(EXTRA_INFO,a);
	}
	
	/**
	 * A callback called when the set of markers should be cleared.
	 * 
	 * @param r The resource whose markers are to be cleared
	 * @throws CoreException
	 */
	static public void clearMarkers(IResource r) throws CoreException {
		if (r.exists()) r.deleteMarkers(ESCJAVA_MARKER_ID,
				false, IResource.DEPTH_INFINITE);
		// false above indicates not to delete subtypes.  
		// Perhaps it should be true, but there are no subtypes
		// defined right now.
	}

	/**
	 * Clears all the markers for the resources in the Collection; does
	 * this within a ResourcesPlugin batch operation
	 * 
	 * @param c A collection of IResource objects
	 * @throws CoreException
	 */
	public static void clearMarkers(final Collection c) throws CoreException {
		ResourcesPlugin.getWorkspace().run(
				new IWorkspaceRunnable() {
					public void run(IProgressMonitor pm) throws CoreException {
						Iterator i = c.iterator();
						while (i.hasNext()) {
							IResource r = (IResource)i.next();
							if (r.exists()) r.deleteMarkers(ESCJAVA_MARKER_ID, false, IResource.DEPTH_INFINITE);
						}
					}
				},null);
	}
	
	/**
	 * Returns the extra information associated with a Marker.
	 * @param m The marker whose infor is to be returned
	 * @return  A List of String containing associated locations
	 * @throws Exception
	 */
	//@ requires m != null;;
	//@ ensures \result != null;
	static public List getExtraInfo(IMarker m) throws Exception {
		List list = new LinkedList();
		String s = (String)m.getAttribute(EXTRA_INFO);
		//System.out.println("EX " + s);
		if (s == null) return list;
		// FIXME - use some sort of string parser
		int k;
		while ((k = s.indexOf(';')) != -1) {
			list.add(s.substring(0,k));
			s = s.substring(k+1);
		}
		list.add(s);
		return list;
	}
	
	static class Provider implements IMarkerImageProvider {
		public String getImagePath(IMarker marker) {
			System.out.println("CALLED");
			return "icons/escjava_prolem.gif";
		}	
	}
	
}

// FIXME - escjava problem markers are off by default?
// FIXME - escjava checking is off by default?
// FIXME - need to appropriately show associated information
// FIXME - get options in preferences
// FIXME - get spec path correct (seems to read built-in specs)
// FIXME - get accelerator keys to work
// FIXME - cleaning should delete all markers
// FIXME - duplicate markers are produced!!!!

// FIXME - clean up positioning of marker

// FIXME - if there is concurrency then the caching of project for jmlFailed is bad

/* Eclipse problem?  When a property page is first brought up
 * by selecting a proejct and Alt-Enter, then when asking for
 * the escjava properties, a warning message comes up. Thereafter
 * things seem to work ok.
 */
