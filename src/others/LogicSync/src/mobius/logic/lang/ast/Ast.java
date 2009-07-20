package mobius.logic.lang.ast;


/** 
 * Base class for the AST hierarchy. 
 *
 * The AST classes are designed to be immutable so that multiple
 * versions of the program can be kept around at the same time,
 * while common parts are shared. Common parts within the same
 * version <i>must not be shared</i>: Many processing stages use
 * a reference to identify the place in the program and this
 * wouldn't work with intra-version sharing. The {@code clone}
 * method should help in situations where you'd be tempted to share.
 *
 * One consequence of enforcing immutability is that the mutable
 * Java collection classes are not used. Instead, singly linked
 * lists are used. These will feel unnatural to OO programmers
 * but natural to functional programmers. Yes, Java is quite verbose
 * for the functional style but it's not terrible. Please try it.
 *
 * @author rgrig
 */
public abstract class Ast implements Cloneable {
  /** The location of this AST node. */
  protected FileLocation location;
  
  /**
   * Returns the location of this AST node. 
   * @return the location of this AST node.
   */
  public FileLocation loc() {
    return location;
  }

  /**
   * Returns a clone of this AST.
   */
  abstract public Ast clone();
}
