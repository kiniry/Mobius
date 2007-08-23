/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Aug 8, 2004
 */
package escjava.plugin;

import org.eclipse.core.resources.IMarker;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;

/**
 * @author David Cok
 *
 * TODO Implement quick fixes for Escjava warnings
 */
public class MarkerResolutionGenerator 
		implements IMarkerResolutionGenerator {

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IMarkerResolutionGenerator#getResolutions(org.eclipse.core.resources.IMarker)
	 */
	public IMarkerResolution[] getResolutions(IMarker marker) {
		return new IMarkerResolution[0];
	}

}
