package mobius.directVCGen.formula.jmlTranslator;

import java.util.HashSet;
import java.util.Properties;

import javafe.ast.FieldAccess;
import javafe.ast.Identifier;
import mobius.directVCGen.formula.Type;

/** Properties that are passed as argument of the visitor. */
final class GlobalProperties extends Properties {
  /** */
  private static final long serialVersionUID = 1L;

  /** valid properties string. */
  private static final String [] validStr = {
    "classId",
    "doSubsetChecking"
  };
  
  final java.util.Set<Type> visibleTypeSet = new HashSet<Type>();
  
  /** tell wether or not annotations are being currently inspected. */
  boolean interesting;
  
  /** tell wether or not a predicate are being currently inspected. */
  boolean pred =  true;
  
  /** tell wether or not we are being currently inside a fresh annotation. */
  boolean fresh = false;

  final HashSet<FieldAccess> subsetCheckingSet = new HashSet<FieldAccess>();
  
  public GlobalProperties() {
    initProperties(); 
  }
  
  private void initProperties() {
    put("doSubsetChecking", Boolean.FALSE); 
    put("classId", Identifier.intern(""));       
  }
  
  @Override
  public Object put (final Object key, final Object value) {
    for (String valid: validStr) {
      if (key.equals(valid)) {
        return super.put(key, value);
      }
    }
    throw new IllegalArgumentException("Invalid key: " + key);
  }
}