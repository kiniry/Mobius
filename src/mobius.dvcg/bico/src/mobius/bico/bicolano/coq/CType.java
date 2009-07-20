package mobius.bico.bicolano.coq;

import mobius.bico.Util;
import mobius.bico.bicolano.AType;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;

/**
 * This class represents a Coq Type.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CType extends mobius.bico.bicolano.AType {
  /** the Coq representation of the type. */
  private final String fStr;
  
  public CType(final Type t, final Repository repos) throws ClassNotFoundException {
    super("CoqType");
    if (t instanceof BasicType) {
      fStr = "(PrimitiveType " + convertPrimitiveType((BasicType) t) + ")";
    } 
    else if (t instanceof ReferenceType) {
      fStr = "(ReferenceType " + convertReferenceType((ReferenceType) t, repos) + ")";
    } 
    else {
      Util.unhandled("Unhandled Type: ", t);
      fStr = "(ReferenceType (ObjectType javaLangObject " + 
                        Translator.comment(t.toString()) + " )";
    }
  }


  public CType() {
    super("CoqType");
    fStr = "CoqType";
  }

  /**
   * Converts a primitive type to a string.
   * @param t the type to convert
   * @return Coq value of t of type primitiveType
   */
  public PrimType convertPrimitiveType(final BasicType t) {
    if (t.equals(Type.BOOLEAN) || t == Type.BYTE || 
        t == Type.SHORT || t == Type.INT) {
      return new PrimType(t.toString().toUpperCase());
    } 
    else {
      Util.unhandled("BasicType", t);
      return new PrimType("INT " + Translator.comment(t.toString()));
    }
  }
  
  
  /**
   * Convert a type to a Coq valid type.
   * 
   * @param t
   *            the type to convert
   * @param repos
   *            is the repository where information on classes can be found
   * @return Coq value of t of type type
   * @throws ClassNotFoundException
   *             if the type cannot be resolved
   */
  public AType convertType(final Type t, final Repository repos)
    throws ClassNotFoundException {
    return new CType(t, repos);
    
  }
  /**
   * @param type
   *            the type to convert
   * @param repos
   *            is the repository where information on classes can be found
   * @return Coq value of t of type refType
   * @throws ClassNotFoundException
   *             if a type cannot have its class resolved
   */
  public RefType convertReferenceType(final ReferenceType type,
                                            final Repository repos) 
    throws ClassNotFoundException {
    final RefType convertedType;
    if (type instanceof ArrayType) {
      convertedType = new CRefType((ArrayType) type, repos);
    } 
    else if (type instanceof ObjectType) {
      final ObjectType ot = (ObjectType) type;
      convertedType = new CRefType(ot, repos);
    } 
    else {
      Util.unhandled("ReferenceType", type);
      convertedType = new RefType("(ObjectType javaLangObject " +
                        Translator.comment(type.toString()) + " )");
    }
    return convertedType;
  }
  
  /** {@inheritDoc} */
  public String toString() {
    return fStr;
  }
  
  
  public static class CPrimType extends PrimType {

    public CPrimType(String str) {
      super(str);
    }
    
  }
  public static class CRefType extends RefType {
    public CRefType(ArrayType type, final Repository repos) 
      throws ClassNotFoundException {
      
      final String convertedType = "(ArrayType " + 
                          getInstance().convertType(type.getElementType(), repos) + ")";
      setStr(convertedType);
    }
    
    public CRefType(ObjectType type, final Repository repos) 
      throws ClassNotFoundException {
      
      final String convertedType;
      if (type.referencesInterfaceExact()) {
        convertedType = "(InterfaceType " + Util.coqify(type.getClassName()) + "Type.name)";
      } 
      else {
        convertedType = "(ClassType " + Util.coqify(type.getClassName()) + "Type.name)";
      }
      setStr(convertedType);
    }
    
  }
  
}
