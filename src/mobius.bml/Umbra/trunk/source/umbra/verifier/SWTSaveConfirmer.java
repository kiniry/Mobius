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

import umbra.lib.GUIMessages;

/**
 * This class is used during saving a bytecode file. If a
 * bytecode verification error occurs it creates dialog
 * window which asks user whether to proceed with saving the
 * file or not.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class SWTSaveConfirmer extends SaveConfirmer {

  /**
   * Verifier which does verification.
   */
  private BytecodeVerifier my_verifier;

  /**
   * Parent shell.
   */
  private Shell my_shell;

  /**
   * Creates graphical save confirmer used during saving a bytecode
   * file.
   *
   * @param a_result_presenter presenter with verification output
   * @param a_shell parent shell
   */
  public SWTSaveConfirmer(final ResultPresenter a_result_presenter,
                          final Shell a_shell) {
    super(a_result_presenter);
    my_verifier = a_result_presenter.getVerifier();
    this.my_shell = a_shell;
  }

  /**
   * This method is called during saving a bytecode file. If a
   * bytecode verification error occurs it creates dialog
   * window which asks user whether to proceed with saving the
   * file or not.
   *
   * @return <code>true</code> if there weren't any verification
   * errors, user decision otheriwse
   */
  @Override
  public boolean confirm() {
    if (!my_verifier.passed()) {
      getResultPresenter().presentAll();
      final MessageBox msgBox =
        new MessageBox(my_shell, SWT.ICON_QUESTION | SWT.YES | SWT.NO);
      msgBox.
      setMessage(GUIMessages.VERIFICATION_ERROR_MESSAGE);
      msgBox.setText(GUIMessages.VERIFICATION_MESSAGE_TITLE);
      final int res = msgBox.open();
      return (res == SWT.YES);
    } else {
      return true;
    }
  }

}
