package mobius.directvcgen.translator.struct;

import java.util.HashSet;
import java.util.Set;

import javafe.ast.FieldAccess;
import javafe.ast.Identifier;

/**
 * Properties that are passed as argument of the visitor.
 * Made to replace Claudia's properties use. 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class GlobalProperties {
  /** */
  private static final long serialVersionUID = 1L;
  
  private final Set< org.apache.bcel.generic.Type> fVisibleTypeSet = 
    new HashSet< org.apache.bcel.generic.Type>();
  
  private final Set<FieldAccess> subsetCheckingSet = 
    new HashSet<FieldAccess>();

  /** the currently inspected class identifier. */
  private Identifier fClassId = Identifier.intern("");
  




  /**
   * Returns the current class id
   * or the id made of the empty string.
   * @return the current class id
   */
  public Identifier getClassId() {
    return fClassId;
  }

  public void setClassId(final Identifier id) {
    fClassId = id;
  }
  
  public void addVisibleTypes(Set<org.apache.bcel.generic.Type> visibleTypeSet) {
    fVisibleTypeSet.addAll(visibleTypeSet);
  }
  
  public Set<org.apache.bcel.generic.Type> getVisibleTypes() {
    return fVisibleTypeSet;
  }

  public Set<FieldAccess> getSubsetCheckingSet() {
    return subsetCheckingSet;
  }

  public void clearSubsetCheckingSet() {
    subsetCheckingSet.clear();
  }

  public void addSubsetCheckingSet(FieldAccess fieldAccess) {
    subsetCheckingSet.add(fieldAccess);
  }
}
