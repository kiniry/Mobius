/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.widgets.Shell;

/**
 * This is a factory for graphical save confirmer.
 *
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class MarkerVerificationFactory extends VerificationFactory {

  /**
   *
   */
  private Shell my_shell;

  /**
   * file with bytecode.
   */
  private IFile my_file;

  /**
   * @param a_file file
   * @param a_shell shell
   */
  public MarkerVerificationFactory(final IFile a_file, final Shell a_shell) {
    this.my_file = a_file;
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
    return new MarkerResultPresenter(my_file, a_verifier);
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
