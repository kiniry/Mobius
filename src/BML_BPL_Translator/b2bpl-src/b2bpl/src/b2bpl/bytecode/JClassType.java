package b2bpl.bytecode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import b2bpl.bytecode.bml.ast.BMLConstraint;
import b2bpl.bytecode.bml.ast.BMLInvariant;


public class JClassType extends JReferenceType implements IConstants {

  public static final JClassType[] EMPTY_ARRAY = new JClassType[0];

  private final String name;

  private int accessModifiers;

  private JClassType supertype = null;

  private JClassType[] interfaces;

  private BCField[] fields;

  private BCMethod[] methods;

  private BMLInvariant[] invariants;

  private BMLConstraint[] constraints;

  private HashMap<String, BCField> fieldsMap;

  private HashMap<String, BCMethod> methodsMap;

  public JClassType(String name) {
    this.name = name.replace('/', '.');
  }

  public String getName() {
    return name;
  }

  public String getInternalName() {
    return name.replace('.', '/');
  }

  public String getDescriptor() {
    return "L" + getInternalName() + ";";
  }

  public boolean isClassType() {
    return true;
  }

  public int getAccessModifiers() {
    TypeLoader.loadType(getName());
    return accessModifiers;
  }

  public JClassType getSupertype() {
    TypeLoader.loadType(getName());
    return supertype;
  }

  public JClassType[] getInterfaces() {
    TypeLoader.loadType(getName());
    return interfaces;
  }

  void setTypeInfo(
      int accessModifiers,
      JClassType supertype,
      JClassType[] interfaces) {
    this.accessModifiers = accessModifiers;
    this.supertype = supertype;
    this.interfaces = interfaces;
  }

  public boolean isInterface() {
    return (getAccessModifiers() & ACC_INTERFACE) != 0;
  }

  public boolean isPublic() {
    return (getAccessModifiers() & ACC_PUBLIC) != 0;
  }

  public boolean isPrivate() {
    return (getAccessModifiers() & ACC_PRIVATE) != 0;
  }

  public boolean isProtected() {
    return (getAccessModifiers() & ACC_PROTECTED) != 0;
  }

  public boolean isPackageProtected() {
    return !(isPublic() || isPrivate() || isProtected());
  }

  public boolean isAbstract() {
    return (getAccessModifiers() & ACC_ABSTRACT) != 0;
  }

  public boolean isFinal() {
    return (getAccessModifiers() & ACC_FINAL) != 0;
  }

  public BCField[] getFields() {
    TypeLoader.loadType(getName());
    return fields;
  }

  public BCMethod[] getMethods() {
    TypeLoader.loadType(getName());
    return methods;
  }

  public BMLInvariant[] getInvariants() {
    TypeLoader.loadType(getName());
    return invariants;
  }

  public BMLConstraint[] getConstraints() {
    TypeLoader.loadType(getName());
    return constraints;
  }

  void setDeclarations(
      BCField[] fields,
      BCMethod[] methods,
      BMLInvariant[] invariants,
      BMLConstraint[] constraints) {
    this.fields = fields;
    this.methods = methods;
    this.invariants = invariants;
    this.constraints = constraints;

    fieldsMap = new HashMap<String, BCField>();
    for (BCField field : fields) {
      fieldsMap.put(field.getName(), field);
    }

    methodsMap = new HashMap<String, BCMethod>();
    for (BCMethod method : methods) {
      methodsMap.put(method.getName() + method.getDescriptor(), method);
    }
  }

  public boolean isSubtypeOf(JType type) {
    if (type.isClassType()) {
      if (equals(type)) {
        return true;
      }
      if ((getSupertype() != null) && (getSupertype().isSubtypeOf(type))) {
        return true;
      }
      for (JClassType iface : getInterfaces()) {
        if (iface.isSubtypeOf(type)) {
          return true;
        }
      }
    }
    return false;
  }

  public BCField getField(String name) {
    TypeLoader.loadType(getName());
    return fieldsMap.get(name);
  }

  public BCMethod getMethod(String name, String descriptor) {
    TypeLoader.loadType(getName());
    return methodsMap.get(name + descriptor);
  }

  public BCField lookupField(String name) {
    BCField field = getField(name);
    if (field != null) {
      return field;
    }
    if (getSupertype() != null) {
      field = getSupertype().lookupField(name);
      if (field != null) {
        return field;
      }
    }
    for (JClassType iface : getInterfaces()) {
      field = iface.lookupField(name);
      if (field != null) {
        return field;
      }
    }
    return null;
  }

  public BCMethod lookupMethod(String name, String descriptor) {
    BCMethod method = getMethod(name, descriptor);
    if (method != null) {
      return method;
    }
    if (getSupertype() != null) {
      method = getSupertype().lookupMethod(name, descriptor);
      if (method != null) {
        return method;
      }
    }
    for (JClassType iface : getInterfaces()) {
      method = iface.lookupMethod(name, descriptor);
      if (method != null) {
        return method;
      }
    }
    return null;
  }

  public List<BCMethod> getMethodOverrides(String name, String descriptor) {
    TypeLoader.loadType(getName());
    List<BCMethod> accumMethods = new ArrayList<BCMethod>();
    accumMethodOverrides(name, descriptor, accumMethods);
    return accumMethods;
  }

  private void accumMethodOverrides(
      String name,
      String descriptor,
      List<BCMethod> accumMethods) {
    BCMethod method = getMethod(name, descriptor);
    if (method != null) {
      accumMethods.add(method);
      if (method.isConstructor() || method.isStatic()) {
        return;
      }
    }
    if (getSupertype() != null) {
      getSupertype().accumMethodOverrides(name, descriptor, accumMethods);
    }
    for (JClassType iface : getInterfaces()) {
      iface.accumMethodOverrides(name, descriptor, accumMethods);
    }
  }

  public String toString() {
    return name;
  }
}
