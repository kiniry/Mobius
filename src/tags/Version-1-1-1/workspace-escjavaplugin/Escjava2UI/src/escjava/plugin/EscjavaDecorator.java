/*
 * This file is part of the Esc/Java2 plugin project.
 * Copyright 2004-2005 David R. Cok
 * 
 * Created on Feb 3, 2005
 */
package escjava.plugin;

import java.net.URL;
import java.util.Collection;
import java.util.HashSet;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.osgi.framework.Bundle;

import pluginlib.Log;
import pluginlib.Utils;

/**
 * @author David Cok
 *
 * This class provides a decorator for ICompilationUnit labels,
 * indicating whether they are enabled for Esc/Java checking or not.
 */
public class EscjavaDecorator implements org.eclipse.jface.viewers.ILightweightLabelDecorator {
	/** A cached value of an icon that is used when the
	 *  element is enabled for Esc/Java checking
	 */
	private static ImageDescriptor img = null;
	
	/** A cached value of an icon that is used when the
	 *  element is individually enabled for Esc/Java checking,
	 *  but the project as a whole is disabled.
	 */
	private static ImageDescriptor imgDisabled = null;
	
	// This is called by the system.  Our job is to add to the
	// provided decoration if we deem it appropriate, based on 
	// the state of the given element.
	public void decorate(Object element, IDecoration decoration) {
		if (element instanceof ICompilationUnit) {
			IResource r;
			try {
				ICompilationUnit c = (ICompilationUnit)element;
				// It appears that the DecorationManager does not
				// know when a decorated resource disappears, so we
				// check here.
				// TODO: I'm not sure there is not a latent race condition on deleting resources
				// Perhaps there is some UI threading issue outstanding.
				if (!c.exists()) return;
				r = c.getCorrespondingResource();
			} catch (JavaModelException e) {
				Log.errorlog("Failed to get the resource for a compilation unit " + 
						((ICompilationUnit)element).getElementName(), e);
				return;
			}
			if (!AutoCheckBuilder.isEnabled(r)) return;
			if (img == null) {
				// Note: could possible have some threading problems here
				// but this is always called within the UI thread, so I
				// think we are ok.
				Bundle bundle = Platform.getBundle(EscjavaPlugin.PLUGINID);
				IPath path = new Path("icons/JMLSmall.png");
				URL iconURL = Platform.find(bundle,path);
				img = ImageDescriptor.createFromURL(iconURL);
				path = new Path("icons/JMLSmallDisabled.png");
				iconURL = Platform.find(bundle,path);
				imgDisabled = ImageDescriptor.createFromURL(iconURL);
			}
			try {
        if (Utils.isBuilderEnabled(r.getProject(),
            EscjavaPlugin.ESCJAVA_AUTOCHECK_BUILDER)) {
          decoration.addOverlay(img, IDecoration.TOP_LEFT);
        } else {
          decoration.addOverlay(imgDisabled, IDecoration.TOP_LEFT);
        }
      } catch (CoreException e) {
        Log.errorlog("Exception while testing a project's build specs "
            + r.getProject().getName(), e);
      }
			// TODO: Perhaps this is overkill - we are calling the
			// listeners whether or not we changed:
			// Also it is not clear whether we need to notify anyone or not
//			Iterator i = listeners.iterator();
//			while (i.hasNext()) {
//				ILabelProviderListener p = (ILabelProviderListener)i.next();
				//p.labelProviderChanged(null); // FIXME - null is definitely not ok,
									// but where do we get an event from?
//			}
		}
	}

	/** The interface has methods to add and remove listeners;
	 *  we keep track of them here.
	 */
	private Collection listeners = new HashSet();
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#addListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	public void addListener(ILabelProviderListener listener) {
		listeners.add(listener);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#dispose()
	 */
	public void dispose() {
		// ImageDescriptors do not need to be disposed of
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#isLabelProperty(java.lang.Object, java.lang.String)
	 */
	// FIXME - not sure what this method should return
	public boolean isLabelProperty(Object element, String property) {
		return (element instanceof ICompilationUnit) ||
				(element instanceof IJavaProject);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#removeListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	public void removeListener(ILabelProviderListener listener) {
		listeners.remove(listener);
	}
}
