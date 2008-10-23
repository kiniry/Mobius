package mobius.directVCGen.formula;

import javafe.ast.ASTNode;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;

public class PositionHint {
  int bytePos;
  int sourcePos;
  
  public PositionHint(ASTNode node) {
    sourcePos = node.getStartLoc();
    
  }
  public PositionHint(InstructionHandle node) {
    bytePos = node.getPosition();
    
  }
  
  public PositionHint(MethodGen n) {
  }
  public int getStartLoc() {
    return sourcePos;
  }
}
