/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.Type;
import org.apache.bcel.verifier.VerificationResult;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public abstract class ResultPresenter {

  /**
   * verifier used to check bytecode.
   */
  private BytecodeVerifier my_verifier;

  /**
   * @param a_verifier verifier
   */
  public ResultPresenter(final BytecodeVerifier a_verifier) {
    this.my_verifier = a_verifier;
  }

  /**
   *
   * @return current verifier
   */
  public BytecodeVerifier getVerifier() {
    return my_verifier;
  }

  /**
   *
   * @param a_verifier new verifier.
   */
  public void setVerifier(final BytecodeVerifier a_verifier) {
    my_verifier = a_verifier;
  }

  /**
   * presents pass1 verification results.
   */
  public abstract void presentPass1();

  /**
   * presents pass2 verification results.
   */
  public abstract void presentPass2();

  /**
   * presents pass3a verification results.
   */
  public abstract void presentPass3a();

  /**
   * presents pass3b verification results.
   */
  public abstract void presentPass3b();

  /**
   * presents result of whole verification.
   */
  public abstract void presentAll();

  /**
   *
   * @param a_result result of verification process
   * @return info about verification results
   */
  protected String getInfo(final VerificationResult a_result) {
    if (a_result.getStatus() == VerificationResult.VERIFIED_OK) {
      return "OK";
    } else if (a_result.getStatus() == VerificationResult.VERIFIED_REJECTED) {
      return a_result.getMessage();
    } else {
      return "?";
    }
  }

  /**
   *
   * @param a_length number of character forming a line
   * @param a_char   char used to create a line
   * @return string representing a line made of given chars
   */
  protected String line(final int a_length, final char a_char) {
    final StringBuilder sb = new StringBuilder();
    for (int i = 0; i < a_length; i++) {
      sb.append(a_char);
    }
    return sb.toString();
  }

  /**
   *
   * @param a_method method to be presented
   * @return result of method verification
   */
  protected String presentMethod(final Method a_method) {
    final Type ret = a_method.getReturnType();
    final String name = a_method.getName();
    final Type[] args = a_method.getArgumentTypes();
    final StringBuilder sb = new StringBuilder();
    sb.append(ret.toString());
    sb.append(" ");
    sb.append(name);
    sb.append("(");
    for (int i = 0; i < args.length; i++) {
      sb.append(args[i].toString());
      if (i < args.length - 1) {
        sb.append(", ");
      }
    }
    sb.append(")");
    return sb.toString();
  }

}
