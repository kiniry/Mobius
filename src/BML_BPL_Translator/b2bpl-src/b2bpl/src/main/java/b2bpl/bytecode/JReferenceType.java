package b2bpl.bytecode;

import b2bpl.bytecode.bml.ast.BMLInvariant;


public abstract class JReferenceType extends JType {

  public boolean isReferenceType() {
    return true;
  }

  public BCField[] getFields() {
    return BCField.EMPTY_ARRAY;
  }

  public BCMethod[] getMethods() {
    return BCMethod.EMPTY_ARRAY;
  }

  public BMLInvariant[] getInvariants() {
    return BMLInvariant.EMPTY_ARRAY;
  }

  public BCField getField(String name) {
    return null;
  }

  public BCMethod getMethod(String name, String descriptor) {
    return null;
  }

  public BCField lookupField(String name) {
    return null;
  }

  public BCMethod lookupMethod(String name, String descriptor) {
    return null;
  }
}
