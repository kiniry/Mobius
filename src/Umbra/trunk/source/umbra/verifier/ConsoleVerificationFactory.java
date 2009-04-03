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
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConsoleVerificationFactory extends VerificationFactory {

  /**
   * 
   */
  @Override
  public ResultPresenter getResultPresenter(BytecodeVerifier verifier) {
    return new ConsoleResultPresenter(verifier);
  }

  /**
   * 
   */
  @Override
  public SaveConfirmer getSaveConfirmer(ResultPresenter resultPresenter) {
    return new SWTSaveConfirmer(resultPresenter); 
  }
}
