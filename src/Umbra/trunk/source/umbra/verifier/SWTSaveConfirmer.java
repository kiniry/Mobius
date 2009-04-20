/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;

/**
 * This class is used during saving a bytecode file. If a
 * bytecode verification error occurs it creates dialog
 * window which asks user whether to proceed with saving the
 * file or not.
 * 
 * TODO (to236111) add window which presents verification results
 * 
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class SWTSaveConfirmer extends SaveConfirmer {
  
  private BytecodeVerifier verifier;
  private Shell a_shell;
  
  /**
   * Creates graphical save confirmer used during saving a bytecode
   * file.
   * 
   * @param resultPresenter presenter with verification output
   */
  public SWTSaveConfirmer(ResultPresenter resultPresenter, Shell a_shell) {
    super(resultPresenter);
    verifier = resultPresenter.verifier;
    this.a_shell = a_shell;
  }
 
  /**
   * This method is called during saving a bytecode file. If a
   * bytecode verification error occurs it creates dialog
   * window which asks user whether to proceed with saving the
   * file or not
   * 
   * TODO (to236111) add constants in GUIMessages for error message
   * and window title
   * 
   * @return <code>true</code> if there weren't any verification
   * errors, user decision otheriwse
   */
  @Override
  public boolean confirm() {
    if (!verifier.passed()) {
      resultPresenter.presentAll();
      MessageBox msgBox = new MessageBox(a_shell, SWT.ICON_QUESTION | SWT.YES | SWT.NO);
      msgBox.setMessage("Errors occured during bytecode verification. Save anyway?");
      msgBox.setText("Verification errors");
      int res = msgBox.open();
      return (res == SWT.YES);
    } else {
      return true;
    }
  }
  
}
