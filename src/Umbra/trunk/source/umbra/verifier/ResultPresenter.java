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
interface ResultPresenter {
  
  /**
   * presents pass1 verification results
   * @param verifier 
   */
  public void presentPass1(BytecodeVerifier verifier);
  
  /**
   * presents pass2 verification results
   * @param verifier 
   */
  public void presentPass2(BytecodeVerifier verifier);
  
  /**
   * presents pass3a verification results
   * @param verifier 
   */
  public void presentPass3a(BytecodeVerifier verifier);
  
  /**
   * presents pass3b verification results
   * @param verifier 
   */
  public void presentPass3b(BytecodeVerifier verifier);
  
  /**
   * presents result of whole verification
   * @param verifier 
   */
  public void presentAll(BytecodeVerifier verifier);
  
}
