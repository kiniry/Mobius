/*
 * Copyright  2000-2004 The Apache Software Foundation
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); 
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License. 
 *
 */ 
package org.apache.bcel.verifier.exc;


/**
 * Instances of this class are thrown by BCEL's class file verifier "JustIce"
 * when a class file to verify does not pass the verification pass 2 as described
 * in the Java Virtual Machine specification, 2nd edition.
 *
 * @version $Id: ClassConstraintException.java 371539 2006-01-23 14:08:00Z tcurdt $
 * @author Enver Haase
 */
public class ClassConstraintException extends VerificationException{
  
  /**
   * The number of method for which the error occurred. -1 if no method is
   * appropriate.
   */
  private int methodNo;
  
	/**
	 * Constructs a new ClassConstraintException with null as its error message string.
	 */
	public ClassConstraintException(){
		super();
		methodNo = -1;
	}
	
	/**
	 * Constructs a new ClassConstraintException with the specified error message.
	 * @param i 
	 */
	public ClassConstraintException(String message){
		super (message);
		methodNo = -1;
	}
	
	 
  /**
   * Constructs a new ClassConstraintException with the specified error message
   * and method number for which the error occurred.  
   * @param method the method for which the error occurred
   */
  public ClassConstraintException(String message, int method){
    super (message);
    methodNo = method;
  }

  /**
   * @return the method number for which 
   */
  public int getMethodNo() {
    return methodNo;
  }
}
