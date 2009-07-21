/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.swt.widgets.Shell;

/**
 * This is a factory for graphical save confirmer.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class SWTVerificationFactory extends VerificationFactory {

  /**
   *
   */
  private Shell my_shell;

  /**
   * @param a_shell shell
   */
  public SWTVerificationFactory(final Shell a_shell) {
    this.my_shell = a_shell;
  }

  /**
   * Creates new result presenter for given verifier.
   *
   * @return presenter for results of verification
   * @param  a_verifier verifier
   */
  @Override
  public ResultPresenter getResultPresenter(final BytecodeVerifier a_verifier) {
    return new SWTResultPresenter(a_verifier, my_shell);
  }

  /**
   * Creates new save confirmer.
   *
   * @return object responsible for asking user if she wants to save
   * in spite of verification trouble
   * @param  a_result_presenter presenter
   */
  @Override
  public SaveConfirmer getSaveConfirmer(
            final ResultPresenter a_result_presenter) {
    return new SWTSaveConfirmer(a_result_presenter, my_shell);
  }
}
