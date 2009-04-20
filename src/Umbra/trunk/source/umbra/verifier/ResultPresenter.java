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
  
  protected String getInfo(VerificationResult result) {
    if (result.getStatus() == VerificationResult.VERIFIED_OK) {
      return "OK";
    } else if (result.getStatus() == VerificationResult.VERIFIED_REJECTED) {
      return result.getMessage();
    } else {
      return "?";
    }
  }
  
  protected String line(int n, char c) {
    StringBuilder sb = new StringBuilder();
    for (int i=0; i < n; i++) {
      sb.append(c);
    }
    return sb.toString();
  }
  
  protected String presentMethod(Method m) {
    Type ret = m.getReturnType();
    String name = m.getName();
    Type[] args = m.getArgumentTypes();
    StringBuilder sb = new StringBuilder();
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
