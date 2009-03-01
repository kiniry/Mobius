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
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.Type;
import org.apache.bcel.verifier.VerificationResult;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConsoleResultPresenter extends ResultPresenter {

  /**
   * @param verifier
   */
  public ConsoleResultPresenter(BytecodeVerifier verifier) {
    super(verifier);
  }
  
  private void out(Object o) {
    System.out.println(o.toString());
  }
  
  private String getInfo(VerificationResult result) {
    if (result.getStatus() == VerificationResult.VERIFIED_OK) {
      return "OK";
    } else if (result.getStatus() == VerificationResult.VERIFIED_REJECTED) {
      return result.getMessage();
    } else {
      return "?";
    }
  }
  
  private String line(int n, char c) {
    StringBuilder sb = new StringBuilder();
    for (int i=0; i < n; i++) {
      sb.append(c);
    }
    return sb.toString();
  }
  
  
  /**
   */
  public void presentPass1() {
    out("pass1:");
    out(line(40, '-'));
    VerificationResult result = verifier.doPass1();
    out(getInfo(result));
    out("");
  }

  /**
   */
  public void presentPass2() {
    out("pass2:");
    out(line(40, '-'));
    VerificationResult result = verifier.doPass2();
    out(getInfo(result));
    out("");
  }
  
  private String presentMethod(Method m) {
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

  /** 
   * 
   */
  public void presentPass3a() {
    out("pass3a:");
    out(line(40, '-'));
    JavaClass jc = verifier.getJavaClass();
    Method[] methods = jc.getMethods();
    for (int i=0; i < methods.length; i++) {
      VerificationResult result = verifier.doPass3a(i);
      out(presentMethod(methods[i]) + " " + getInfo(result));
    }
    out("");
  }

  /** 
   */
  public void presentPass3b() {
    out("pass3b:");
    out(line(40, '-'));
    JavaClass jc = verifier.getJavaClass();
    Method[] methods = jc.getMethods();
    for (int i=0; i < methods.length; i++) {
      VerificationResult result = verifier.doPass3b(i);
      out(presentMethod(methods[i]) + " " + getInfo(result));
    }    
    out("");
  }

  /**
   */
  public void presentAll() {
    presentPass1();
    presentPass2();
    presentPass3a();
    presentPass3b();
  }



}
