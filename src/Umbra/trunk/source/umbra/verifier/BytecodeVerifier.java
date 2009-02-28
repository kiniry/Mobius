/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;



import org.apache.bcel.Repository;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.verifier.VerificationResult;
import org.apache.bcel.verifier.Verifier;
import org.apache.bcel.verifier.VerifierFactory;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeVerifier {
  
  private Verifier verifier;
  
  private JavaClass jc;

  /**
   * @return java class
   */
  public JavaClass getJavaClass() {
    return jc;
  }
  
  /**
   * @param jc class to verify
   */
  public BytecodeVerifier(JavaClass jc) {
    this.jc = jc;
    Repository.clearCache();
    Repository.addClass(jc);
    String class_name = jc.getClassName();
    verifier = VerifierFactory.getVerifier(class_name);
    verifier.flush();
  }
  
  /**
   * @return result of pass 1 verification
   */
  public VerificationResult doPass1() {
    return verifier.doPass1();
  }
  
  /**
   * @return result of pass 2 verification
   */
  public VerificationResult doPass2() {
    return verifier.doPass2();
  }
  
  /**
   * @param  method_no index of method to verify
   * @return result of pass 3a verification
   */
  public VerificationResult doPass3a(int method_no) {
    return verifier.doPass3a(method_no);
  }
  
  /**
   * @param  method_no index of method to verify
   * @return result of pass 3b verification
   */
  public VerificationResult doPass3b(int method_no) {
    return verifier.doPass3b(method_no);
  }
  
  /**
   * @return true if verification passed false otherwise
   */
  public boolean passed() {
    if (doPass1().getStatus() != VerificationResult.VERIFIED_OK) return false;
    if (doPass2().getStatus() != VerificationResult.VERIFIED_OK) return false;
    
    for (int i = 0; i < jc.getMethods().length; i++) {
      if (doPass3a(i).getStatus() != VerificationResult.VERIFIED_OK) return false;
      if (doPass3b(i).getStatus() != VerificationResult.VERIFIED_OK) return false;
    }
    return true;
  }
    
}
