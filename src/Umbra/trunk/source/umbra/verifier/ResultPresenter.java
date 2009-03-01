/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
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
public abstract class ResultPresenter {
  
  protected BytecodeVerifier verifier;
  
  /**
   * @param verifier
   */
  public ResultPresenter(BytecodeVerifier verifier) {
    this.verifier = verifier;
  }
  
  /**
   * presents pass1 verification results 
   */
  public abstract void presentPass1();
  
  /**
   * presents pass2 verification results
   */
  public abstract void presentPass2();
  
  /**
   * presents pass3a verification results
   */
  public abstract void presentPass3a();
  
  /**
   * presents pass3b verification results
   */
  public abstract void presentPass3b();
  
  /**
   * presents result of whole verification
   */
  public abstract void presentAll();
  
}
