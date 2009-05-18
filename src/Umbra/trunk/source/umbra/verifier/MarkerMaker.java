/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class MarkerMaker {

  /**
   *
   * @param a_resource resource to which we attach the marker
   * @param a_msg message to be attached to the marker
   * @param a_line_number number of line where to put the marker
   * @return new marker used to mark errors in bytecode
   */
  public IMarker createMarker(final IResource a_resource,
                               final int a_line_number, final String a_msg) {
    try {
      final IMarker marker = a_resource.createMarker(null);
      marker.setAttribute(IMarker.MESSAGE, a_msg);
      marker.setAttribute(IMarker.LINE_NUMBER, a_line_number);
      return marker;
    } catch (CoreException e) {
      return null;
    }
  }

}
