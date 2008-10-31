package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.Map;

/**
 * This class can be used to decorate nodes of the BCEL tree.
 * Actually it simulates this decoration with hash map structure.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class ADecoration {
  /** the map between the nodes and the 
      objects which decorates the tree. */
  private Map<PositionHint, Object> fMap = 
    new HashMap<PositionHint, Object>();
  
  /** the name of the decoration. */
  private String fName;
  
  /**
   * Creates a decoration with a name used to represent it.
   * @param str the name of the decoration
   */
  public ADecoration(final String str) {
    fName = str;
  }

  /**
   * Return the decoration associated with the given node,
   * or null if there is none.
   * @param n the position of the node
   * @return an object
   */
  protected Object get(final PositionHint n) {
    return fMap.get(n);
  }

  /**
   * Set the decoration for the given node.
   * @param n the node
   * @param obj the decoration to set
   */
  protected void set(final PositionHint n, final Object obj) {
    fMap.put(n, obj);
  }

  /** {@inheritDoc} */
  public String toString() {
    return fName + " " + fMap;
  }

}
