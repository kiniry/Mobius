package mobius.directVCGen.formula;

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
  int bytePos;
  int sourcePos;
  
  /** the full method name, it is of the form  a.b.c.Class.method. */
  private String fFullMethodName;
  
  /** the string representation of the position hint. */
  private String fStrRep;
  
  public PositionHint(ASTNode node) {
    sourcePos = node.getStartLoc();
    
  }
  
  public PositionHint(final MethodGen met) {
    fFullMethodName = met.getClassName() + "." + met.getName();
  }
  
  
  public PositionHint(MethodGen met, InstructionHandle ih) {
    this(met);
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
      fStrRep = fFullMethodName + " " + bytePos + " " + sourcePos;
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
}
