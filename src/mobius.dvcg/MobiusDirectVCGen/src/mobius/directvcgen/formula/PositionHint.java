package mobius.directvcgen.formula;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;

/**
 * A small structure representing a source and bytecode position,
 * inside a method.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */

public class PositionHint {

  
  /** the list of hints representing methods. */
  private static Map<String, MethodHint> methodHint = 
      new HashMap<String, MethodHint>();
  
  /** the offset in the bytecode, relative to the method. */
  private int fBytePos;
  
  /** the full method name, it is of the form  a.b.c.Class.method. */
  private String fFullMethodName;
  
  /** the string representation of the position hint. */
  private String fStrRep;
  
  /**
   * Build a position hint used to represent a method. Internal
   * use only.
   * @param met the method 
   * @see mobius.directVCGen.formula.MethodHint
   */
  private PositionHint(final MethodGen met) {
    if (met == null) {
      throw new IllegalArgumentException("The method cannot be null!");
    }
    fFullMethodName = getFullMethodName(met);
  }


  private static String getFullMethodName(final MethodGen met) {
    String types = "";
    for (org.apache.bcel.generic.Type typ: met.getArgumentTypes()) {
      types += ", " + typ;
    }
    if (!types.equals("")) {
      types = types.substring(2);
    }
    return met.getClassName() + "." + met.getName() + 
                        "(" + types + ")";
  }
  

  /**
   * Creates a position hint relative to an instruction.
   * @param met the method in which the instruction lies
   * @param ih the instruction to get the position hint from
   */
  public PositionHint(final MethodGen met, final InstructionHandle ih) {
    this(met);
    fBytePos = ih.getPosition();
  }
  

  /** {@inheritDoc} */
  @Override
  public int hashCode() {
    return this.toString().hashCode();
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    if (fStrRep == null) {
      fStrRep = "Base " + fFullMethodName + " " + fBytePos;
    }
    return fStrRep;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean equals(final Object o) {
    if (o instanceof PositionHint) {
      final PositionHint ph = (PositionHint) o;
      return fFullMethodName.equals(ph.fFullMethodName) &&
              (fBytePos == ph.fBytePos);
    }
    return false;
  }


  /**
   * Returns a method hint corresponding to the given method.
   * Cannot return null.
   * @param met The method to wrap in a position hint 
   * @return the position hint corresponding to the method.
   */
  public static MethodHint getMethodPositionHint(final MethodGen met) {
    final String fullMethodName = getFullMethodName(met);
    MethodHint mh = methodHint.get(fullMethodName);
    if (mh == null) {
      mh = new MethodHint(met);
      methodHint.put(fullMethodName, mh);
    }
    return mh;
  }
  
  /**
   * The list of mehod hints which have been collected.
   * @return a collection of method hint. This can be empty.
   */
  public static Collection<MethodHint> getMethodPositionList() {
    return methodHint.values();
  }
  
  /**
   * The list of methods which have been collected.
   * @return a set of method
   */
  public static Set<MethodGen> getMethodList() {
    final Set<MethodGen> res = new HashSet<MethodGen>();
    for (MethodHint mh : getMethodPositionList()) {
      res.add(mh.getMethod());
    }
    return res;
  }
  
  /**
   * The class representing a method hint. Used to handle pre and post
   * conditions.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class MethodHint extends PositionHint {
    /** the method which this hint represents. */
    private final MethodGen fMeth;
    /** the string representation of the position hint. */
    private String fStrRep;
    
    /**
     * Construct a new hint.
     * @param met the method to initialize the structure with
     */
    public MethodHint(final MethodGen met) {
      super(met);
      fMeth = met;
      fStrRep = "Method " + getFullMethodName(met);
    }

    /**
     * Return the method this hint represents. 
     * @return the method associated with the hint
     */
    public MethodGen getMethod() {
      return fMeth;
    }
    
    /** {@inheritDoc} */
    public String toString() {
      return fStrRep;
    }
  }

  /**
   * The byte code offset used for this hint.
   * @return a non negative integer, which is a valid offset.
   * It corresponds to {@link InstructionHandle#getPosition()}.
   */
  public int getPostion() {
    return fBytePos;
  }
  
}
