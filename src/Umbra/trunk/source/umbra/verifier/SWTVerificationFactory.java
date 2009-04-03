/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

/**
 * This is a factory for graphical save confirmer.
 * 
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class SWTVerificationFactory extends VerificationFactory {

  /**
   * Creates new result presenter for given verifier.
   * 
   * FIXME (to236111): change to graphical presenter
   * 
   * @return presenter for results of verification
   * @param  verifier
   */
  @Override
  public ResultPresenter getResultPresenter(BytecodeVerifier verifier) {
    return new ConsoleResultPresenter(verifier);
  }

  /**
   * Creates new save confirmer.
   * 
   * @return object responsible for asking user if she wants to save
   * in spite of verification trouble
   * @param  resultPresenter
   */
  @Override
  public SaveConfirmer getSaveConfirmer(ResultPresenter resultPresenter) {
    return new SWTSaveConfirmer(resultPresenter); 
  }
}
