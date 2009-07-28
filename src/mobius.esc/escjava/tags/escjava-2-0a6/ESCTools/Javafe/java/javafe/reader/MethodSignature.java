/* Copyright 2000, 2001, Compaq Computer Corporation */

/* =========================================================================
 * MethodSignature.java
 * ========================================================================= */

package javafe.reader;

import java.io.*;
import java.util.*;

import javafe.ast.*;
import javafe.util.*;

/* -------------------------------------------------------------------------
 * MethodSignature
 * ------------------------------------------------------------------------- */

/**
 * Represents the signature of a method in terms of AST elements.
 */

class MethodSignature
{
  /* -- package instance methods ------------------------------------------- */

  /**
   * Construct a new method signature with an empty sequence of parameter
   * types and a void return type.
   */
  //@ requires classLocation != Location.NULL
  MethodSignature(int classLocation)
  {
    this.parameters = new Vector();
    this.return_    = PrimitiveType.make(TagConstants.VOIDTYPE, classLocation);

    //@ set parameters.elementType = \type(Type)
    //@ set parameters.containsNull = false
  }

  /**
   * Count the number of parameter types in this method signature.
   * @return  the number of parameter types
   */
  //@ ensures \result>=0
  //@ ensures \result==parameters.elementCount
  int countParameters()
  {
    return parameters.size();
  }

  /**
   * Return a parameter type from this method signature.
   * @param index  the index of the parameter type to return
   * @return       the parameter type at index index
   */
  //@ requires 0<=index && index<parameters.elementCount
  //@ ensures \result != null;
  //@ ensures \result.syntax
  Type parameterAt(int index)
  {
    return (Type)parameters.elementAt(index);
  }    //@ nowarn Post  // Unenforceable invariant on parameters

  /**
   * Append a parameter type to this method signature.
   * @param type  the parameter type to append
   */
  //@ requires parameter != null;
  //@ requires parameter.syntax
  void appendParameter(Type parameter)
  {
    parameters.addElement(parameter);
  }

  /**
   * Return the return type of this method signature.
   * @return  the return type
   */
  //@ ensures \result != null;
  //@ ensures \result.syntax
  Type getReturn()
  {
    return return_;
  }

  /**
   * Change the return type of this method signature.
   * @param return_  the new return type
   */
  //@ requires return_ != null;
  //@ requires return_.syntax
  void setReturn(Type return_)
  {
    this.return_ = return_;
  }

  /* -- private instance variables ----------------------------------------- */

  /**
   * The parameter types of this method signature.
   * Initialized by constructor.
   */
  //@ invariant parameters != null;
  //@ invariant parameters.elementType == \type(Type)
  //@ invariant !parameters.containsNull
  // Unenforceable invariant: contents are syntax
  /*@spec_public*/ private Vector parameters;

  /**
   * The return type of this method signature.
   * Initialized by constructor.
   */
  //@ invariant return_ != null;
  //@ invariant return_.syntax
  private Type return_;

  /* -- private class variables -------------------------------------------- */

  /**
   * The primitive void type.
   */
  //@ invariant voidType != null;
  private static final Type voidType =
    PrimitiveType.makeNonSyntax(TagConstants.VOIDTYPE);
}

