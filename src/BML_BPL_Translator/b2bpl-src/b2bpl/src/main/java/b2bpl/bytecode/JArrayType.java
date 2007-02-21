package b2bpl.bytecode;


public class JArrayType extends JReferenceType {

  private final JType componentType;

  private final int dimension;

  public JArrayType(JType componentType, int dimension) {
    this.componentType = componentType;
    this.dimension = dimension;
  }

  public JType getComponentType() {
    return componentType;
  }

  public int getDimension() {
    return dimension;
  }

  public JType getIndexedType() {
    if (dimension == 1) {
      return componentType;
    }
    return new JArrayType(componentType, dimension - 1);
  }

  public String getName() {
    return toString();
  }

  public String getInternalName() {
    return getDescriptor();
  }

  public String getDescriptor() {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < dimension; i++) {
      sb.append('[');
    }
    sb.append(componentType.getDescriptor());
    return sb.toString();
  }

  public boolean isArrayType() {
    return true;
  }

  public boolean isSubtypeOf(JType type) {
    if (type.isArrayType()) {
      JArrayType arrayType = (JArrayType) type;
      if (dimension == arrayType.dimension) {
        return componentType.isSubtypeOf(arrayType.componentType);
      } else if (dimension < arrayType.dimension) {
        return false;
      } else {
        type = arrayType.componentType;
      }
    }
    return type.equals(TypeLoader.getClassType("java.lang.Object"))
           || type.equals(TypeLoader.getClassType("java.lang.Cloneable"))
           || type.equals(TypeLoader.getClassType("java.io.Serializable"));
  }

  public BCField lookupField(String name) {
    JClassType object = TypeLoader.getClassType("java.lang.Object");
    return object.lookupField(name);
  }

  public BCMethod lookupMethod(String name, String descriptor) {
    JClassType object = TypeLoader.getClassType("java.lang.Object");
    return object.lookupMethod(name, descriptor);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();
    sb.append(componentType.toString());
    for (int i = 0; i < dimension; i++) {
      sb.append("[]");
    }
    return sb.toString();
  }
}
