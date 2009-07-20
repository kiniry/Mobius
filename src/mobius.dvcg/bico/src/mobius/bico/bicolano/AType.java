package mobius.bico.bicolano;

import mobius.bico.bicolano.coq.CType;

import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;

public abstract class AType extends Translation {
  
  private static AType instance = new CType();
  
  public AType(final String str) {
    super(str);
  }

  public  static class PrimType  extends Translation {
    public PrimType(final String str) {
      super(str);
    }
    public PrimType() {
      super();
    }
  }
  
  public static class RefType extends Translation {
    public RefType(String str) {
      super(str);
    }
    public RefType() {
      super();
    }
  } 
  
  /**
   * Converts a primitive type to a string.
   * @param t the type to convert
   * @return the translated value of t of type primitiveType
   */
  public abstract PrimType convertPrimitiveType(final BasicType t);
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
  public abstract AType convertType(final Type t, final Repository repos)
    throws ClassNotFoundException;

  /**
   * @param type
   *            the type to convert
   * @param repos
   *            is the repository where information on classes can be found
   * @return Coq value of t of type refType
   * @throws ClassNotFoundException
   *             if a type cannot have its class resolved
   */
  public abstract RefType convertReferenceType(final ReferenceType type,
                                            final Repository repos)
    throws ClassNotFoundException;
  public static AType getInstance() {
    return instance;
  } 
 

}
