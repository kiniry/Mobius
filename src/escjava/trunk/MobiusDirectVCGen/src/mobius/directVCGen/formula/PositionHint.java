package mobius.directVCGen.formula;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javafe.ast.ASTNode;

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
  
  private int bytePos;
  private int sourcePos;
  
  /** the full method name, it is of the form  a.b.c.Class.method. */
  private String fFullMethodName;
  
  /** the string representation of the position hint. */
  private String fStrRep;
  
  private PositionHint(final MethodGen met) {
    fFullMethodName = met.getClassName() + "." + met.getName();
  }
  
  public PositionHint(MethodGen met, ASTNode node) {
    fFullMethodName = met.getClassName() + "." + met.getName();
    sourcePos = node.getStartLoc();
  }
  
  
  public PositionHint(MethodGen met, InstructionHandle ih) {
    fFullMethodName = met.getClassName() + "." + met.getName();
    bytePos = ih.getPosition();
  }
  
  
  public int getStartLoc() {
    return sourcePos;
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
      fStrRep = "Base" + fFullMethodName + " " + bytePos + " " + sourcePos;
    }
    return fStrRep;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean equals(final Object o) {
    if (o instanceof PositionHint) {
      final PositionHint ph = (PositionHint) o;
      return fFullMethodName.equals(ph.fFullMethodName) &&
              (bytePos == ph.bytePos) &&
              (sourcePos == sourcePos);
    }
    return false;
  }


  
  public static MethodHint getMethodPositionHint(final MethodGen met) {
    final String fullMethodName = met.getClassName() + "." + met.getName();
    MethodHint mh = methodHint.get(fullMethodName);
    if (mh == null) {
      mh = new MethodHint(met);
      methodHint.put(fullMethodName, mh);
    }
    return mh;
  }
  public static Collection<MethodHint> getMethodPositionList() {
    return methodHint.values();
  }
  public static Set<MethodGen> getMethodList() {
    final Set<MethodGen> res = new HashSet<MethodGen>();
    for (MethodHint mh : methodHint.values()) {
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
    private final MethodGen fMeth;

    public MethodHint(MethodGen met) {
      super(met);
      fMeth = met;
    }

    public MethodGen getMethod() {
      return fMeth;
    }
  }
  
}
