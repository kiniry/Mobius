/*
 * This file is part of a set of utility classes for plugin projects.
 * Copyright 2004 David R. Cok
 */
package mobius.util.plugin.widgets;

import mobius.util.plugin.Log;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;


/**
 * This class consists of utility functions for
 * saving properties associated with keys - currently using 
 * IResource persistent properties.
 * 
 * @author David R. Cok
 */
class Props {
  /**
   * Returns the value of a project property as a String,
   * null if it does not exist.
   * 
   * @param q The name of the property.
   * @return The value of the property, or null if the property
   *       does not exist
   */
  //@ requires q != null;
  public static String getProperty(final QualifiedName q) {
    try {
      return ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(q);
    } 
    catch (CoreException e) {
      return null;
    }
  }

  /**
   * Returns the boolean value of a project property (of the given project).
   * As in @link{#setProperty}, boolean-valued properties are encoded with a zero-length
   * string meaning false, and otherwise true.
   * @param q The name of the property.
   * @param def The value to return if the named property does not exist
   * 
   * @return The value of the property
   */
  //@ requires q != null;
  public static boolean getBooleanProperty(final QualifiedName q, final boolean def) {
    final String s = getProperty(q);
    return s == null ? def : s.length() != 0;
  }

  /**
   * Returns the value of the property, returning the default
   * value if the property does not exist.
   * @param q The name of the property
   * @param def The default value to be returned if the property
   *       does not exist.
   * @return The value of the property, or the default value if
   *       the property does not exist.
   */
  //@ requires q != null;
  public static String getStringProperty(final QualifiedName q, final String def) {
    final String s = getProperty(q);
    return s == null ? def : s;
  }

  /**
   * Sets a boolean value for the property with the given 
   * QualifiedName in the current project (returned by
   * getProject()).  Boolean valued properties are encoded
   * with a zero-length string meaning false and otherwise
   * true.
   * 
   * @param q The name of the property
   * @param v The new boolean value of the property
   */
  //@ requires q != null;
  public static void setProperty(final QualifiedName q, final boolean v) {
    try {
      ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(q, v ? "T" : "");
    } 
    catch (CoreException e) {
      Log.errorlog("Failed to set the property " + q, e);
      // Just ignore and continue on
    }
  }

  /**
   * Sets the value of the property with the given name
   * to the value of the given String.
   *
   * @param q The QualifiedName of the property to set
   * @param v The new value of the property
   */
  //@ requires q != null && v != null;
  public static void setProperty(final QualifiedName q, final String v) {
    try {
      ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(q, v);
    } 
    catch (CoreException e) {
      Log.errorlog("Failed to set the property " + q, e);
      // Just ignore and continue on
    }
  }
  
}
