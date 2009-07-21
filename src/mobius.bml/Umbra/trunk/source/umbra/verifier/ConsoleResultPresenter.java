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
import org.apache.bcel.verifier.VerificationResult;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConsoleResultPresenter extends ResultPresenter {

  /**
   * numer of chars used in a line in console presenter.
   */
  private final int my_width = 40;

  /**
   * @param a_verifier verifier used to check bytecode
   */
  public ConsoleResultPresenter(final BytecodeVerifier a_verifier) {
    super(a_verifier);
  }

  /**
   * prints to stdout result of toString() of an object.
   * @param an_object object to be printed
   */
  private void out(final Object an_object) {
    System.out.println(an_object.toString());
  }

  /**
   * prints to stdout results of first phase of verification.
   */
  public void presentPass1() {
    out("pass1:");
    out(line(my_width, '-'));
    final VerificationResult result = getVerifier().doPass1();
    out(getInfo(result));
    out("");
  }

  /**
   */
  public void presentPass2() {
    out("pass2:");
    out(line(my_width, '-'));
    final VerificationResult result = getVerifier().doPass2();
    out(getInfo(result));
    out("");
  }

  /**
   */
  public void presentPass3a() {
    out("pass3a:");
    out(line(my_width, '-'));
    final JavaClass jc = getVerifier().getJavaClass();
    final Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3a(i);
      out(presentMethod(methods[i]) + " " + getInfo(result));
    }
    out("");
  }

  /**
   */
  public void presentPass3b() {
    out("pass3b:");
    out(line(my_width, '-'));
    final JavaClass jc = getVerifier().getJavaClass();
    final Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3b(i);
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
