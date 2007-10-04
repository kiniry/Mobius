package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.HashSet;
import java.util.Properties;

import javafe.ast.FieldAccess;
import javafe.ast.Identifier;
import mobius.directVCGen.formula.Type;

/** Properties that are passed as argument of the visitor. */
public final class GlobalProperties extends Properties {
  /** */
  private static final long serialVersionUID = 1L;

  /** valid properties string. */
  private static final String [] validStr = {
    "doSubsetChecking"
  };
  
  public final java.util.Set<Type> visibleTypeSet = new HashSet<Type>();
  
  /** tell wether or not annotations are being currently inspected. */
  public boolean interesting;
  
  /** tell wether or not a predicate are being currently inspected. */
  public boolean pred =  true;
  
  /** tell wether or not we are being currently inside a fresh annotation. */
  public boolean fresh = false;

  public Identifier classId = Identifier.intern("");
  
  public final HashSet<FieldAccess> subsetCheckingSet = new HashSet<FieldAccess>();
  
  public GlobalProperties() {
    initProperties(); 
  }
  
  private void initProperties() {
    put("doSubsetChecking", Boolean.FALSE);  
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