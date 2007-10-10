package mobius.directVCGen.formula;

import javafe.ast.RoutineDecl;



public class Util {
  public static String getMethodName(RoutineDecl decl) {
    
    return decl.parent.id + "Annotations." + decl.id();
  }
}
