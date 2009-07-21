package b2bpl.translation.helpers;

import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLVariableExpression;

public class ModifiedHeapLocation {

  private BPLVariableExpression ref;
  private BPLExpression location;
  
  public ModifiedHeapLocation(BPLVariableExpression r, BPLExpression l) {
    ref = r;
    location = l;
  }
  
  public BPLVariableExpression getReference() { return ref; }
  
  public BPLExpression getLocation() { return location; }
   
}