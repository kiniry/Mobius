/** Public domain. */

package freeboogie.ast.gen;

import java.util.Set;

import freeboogie.util.Err;

/**
 * Represents an abstract grammag (AG). It is basically a map from
 * class names to {@code AgClass} objects plus a couple of utility
 * methods.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Grammar {
  
  /** Creates a new grammar object. */
  public Grammar() {
    Err.notImplemented();
  }
  
  /**
   * Sets the default base class name. If this method is not called
   * then "Node" is used.
   * 
   * @param name the default base class name
   */
  public void setDefaultBaseClassName(String name) {
    Err.notImplemented();
  }
  
  /**
   * Return the class with the specified name, initializing an 
   * {@code AgClass} object if necessary.
   * 
   * @param name the class name
   * @return the {@code AgClass} object representing the class
   */
  public AgClass getClass(String name) {
    Err.notImplemented();
    return null;
  }
  
  /**
   * Returns a set view of the classes in the grammar. It is a view
   * in the underlying {@code Map}.
   *  
   * @return a set of the classes in the grammar.
   */
  public Set<AgClass> getClasses() {
    Err.notImplemented();
    return null;
  }
  
  /**
   * For testing. (TODO)
   * 
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }

}
