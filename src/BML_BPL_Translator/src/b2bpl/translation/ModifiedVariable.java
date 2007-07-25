package b2bpl.translation;

import b2bpl.bpl.ast.BPLType;

/**
 * Structure to store pairs of variable names and their according BoogiePL type.
 * 
 * @author Samuel Willimann
 */
public class ModifiedVariable {
  private String name;

  private BPLType type;

  public ModifiedVariable(String name, BPLType type) {
    this.name = name;
    this.type = type;
  }

  public String getName() {
    return this.name;
  }

  public BPLType getType() {
    return this.type;
  }

  public boolean equals(Object other) {
    return other instanceof ModifiedVariable
           && name.equals(((ModifiedVariable) other).name)
           && type.equals(((ModifiedVariable) other).type);
  }

  public int hashCode() {
    return ((name != null) ? name.hashCode() : 0) + ((type != null) ? type.hashCode() : 0);
  }

}