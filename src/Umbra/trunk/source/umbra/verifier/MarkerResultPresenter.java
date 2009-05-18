/*
 * @title "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright "(c) 2006-2008 University of Warsaw"
 * @license "All rights reserved. This program and the accompanying materials
 * are made available under the terms of the LGPL licence see LICENCE.txt file"
 */
package umbra.verifier;

import java.util.List;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.verifier.VerificationResult;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 */
public class MarkerResultPresenter extends ResultPresenter {

  /**
   * resource representing verified bytecode.
   */
  private IFile my_file;

  /**
   * object used to instantiate markers. subclasses of
   * MarkerMaker can be used to modify the markers properties etc
   */
  private MarkerMaker my_marker_maker;

  /**
   * list of currently displayed markers.
   */
  private List < IMarker > my_markers;

  /**
   * ctor.
   * @param a_file  file with bytecode
   * @param a_verifier bytecode verifier
   */
  public MarkerResultPresenter(final IFile a_file,
                               final BytecodeVerifier a_verifier) {
    super(a_verifier);
    my_file = a_file;
    my_marker_maker = new MarkerMaker();
  }

  /**
   * removes all the markers stored in markers list.
   */
  private void removeMarkers() {
    for (IMarker m : my_markers) {
      try {
        m.delete();
      } catch (CoreException e) {
        e.printStackTrace();
      }
    }
    my_markers = null;
  }

  /**
   * add all markers.
   */
  @Override
  public void presentAll() {
    removeMarkers();
    presentPass1();
    presentPass2();
    presentPass3a();
    presentPass3b();
  }

  /**
   * add markers from pass1.
   */
  @Override
  public void presentPass1() {
    final VerificationResult result = getVerifier().doPass1();
  }

  /**
   * add markers from pass2.
   */
  @Override
  public void presentPass2() {
    final VerificationResult result = getVerifier().doPass2();
  }

  /**
   * add markers from pass3a.
   */
  @Override
  public void presentPass3a() {
    final JavaClass my_jc = getVerifier().getJavaClass();
    final Method[] methods = my_jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3a(i);
      if (result.getStatus() == VerificationResult.VERIFIED_REJECTED) {
        final String message = result.getMessage();
        final int line_number = 15;
        my_marker_maker.createMarker(my_file, line_number, message);
      }
    }
  }

  /**
   * add markers from pass3b.
   */
  @Override
  public void presentPass3b() {
    final JavaClass jc = getVerifier().getJavaClass();
    final Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3b(i);
    }
  }

}
