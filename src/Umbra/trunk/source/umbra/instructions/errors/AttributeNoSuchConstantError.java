/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.errors;

import org.apache.bcel.classfile.Attribute;

/**
 * This class represents an error of referencing non-existing constant
 * from java class attribute.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class AttributeNoSuchConstantError extends NoSuchConstantError {

  /**
   * Attribute that has references to non-existing constants.
   */
  private Attribute my_cause;

  /**
   *
   * @param an_attribute an attribute that has references to non-existing\
   * constants
   */
  public void setAttribute(final Attribute an_attribute) {
    my_cause = an_attribute;
  }

  /**
   * TODO (Umbra) detailed description.
   *
   * @return description of the cause of the error
   */
  public String[] getCauses() {
    return new String[] {"Attribute, name index: " + my_cause.getNameIndex()};
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    return super.getErrorMessage() + " (attribute)";
  }

}
