/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.Map;
import java.util.Vector;

import logic.Expression.Nullity;
import utils.ModifierManager.ClassType;
import utils.smart.SmartString;

/**
 * Container class for the signature of a method/feature.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class Signature {

  /** Return value. */
  private final SmartString my_return_value;
  /** Does this signature mentions explicit nullity. */
  private boolean my_explicit_nullity;

  /** Formal parameter. */
  private final Map < String , SmartString > my_parameter;

  /**
   * Created a new signature.
   * @param a_return_value return value
   * @param some_formal_params formal parameter
   */
  public Signature(final SmartString a_return_value,
                   final Map < String , SmartString > some_formal_params) {
    my_return_value = a_return_value;
    my_parameter = some_formal_params;
    my_explicit_nullity = false;
  }

  /**
   * Get a BON signature with BON default values.
   * @param a_return_value return value
   * @param some_formal_params formal parameters
   * @return BON signature
   */
  public static final Signature getBonSignature(final SmartString a_return_value,
                                       final Map < String , SmartString > some_formal_params) {
    boolean nul = false;
    if (a_return_value.getNullity() == null) {
      a_return_value.setNullity(Nullity.NULLABLE);
    } else {
      nul = true;
    }

    for (final SmartString s : some_formal_params.values()) {
      if (s.getNullity() == null) {
        s.setNullity(Nullity.NULLABLE);
      } else {
        nul = true;
      }
    }
    final Signature sig = new Signature(a_return_value, some_formal_params);
    sig.my_explicit_nullity = nul;
    return sig;
  }

  /**
   * Get a Java signature with Java default values.
   * @param a_return_value return value
   * @param some_formal_params formal parameters
   * @return Java signature
   */
  public static final Signature getJavaSignature(final SmartString a_return_value,
                                        final Map < String ,
                                        SmartString > some_formal_params) {
    boolean nul = false;
    if (a_return_value.getNullity() == null) {
      a_return_value.setNullity(Nullity.NON_NULL);
    } else {
      nul = true;
    }

    for (final SmartString s : some_formal_params.values()) {
      if (s.getNullity() == null) {
        s.setNullity(Nullity.NON_NULL);
      } else {
        nul = true;
      }
    }
    final Signature sig = new Signature(a_return_value, some_formal_params);
    sig.my_explicit_nullity = nul;
    return sig;
  }

  /**
   * Get retun value.
   * @return the return value
   */
  public final SmartString getReturnValue() {
    return my_return_value;
  }

  /**
   * Get formal parameter.
   * @return the parameters
   */
  public final Map < String , SmartString > getFormalParameter() {
    return my_parameter;
  }

  /**
   * Get formal types.
   * @return formal types
   */
  public final List < SmartString > getFormalTypes() {
    return new Vector < SmartString > (my_parameter.values());
  }

  /**
   * Does this signature use explicit nullity.
   * By this we mean whether the nullity is explicitly mentioned.
   * @return use explicit nullity
   */
  public final boolean explicitNullity() {
    return my_explicit_nullity;
  }

  /**
   * Does this signature use default nullity for its
   * language.
   * @param a_type class type to where this signature belongs
   * @return true if default nullity is used
   */
  public final boolean defaultParameterNullity(final ClassType a_type) {
    if (a_type == ClassType.BON) { //default is nullable, so search for non_null
      for (final SmartString s : my_parameter.values()) {
        if (s.getNullity() == Nullity.NON_NULL) {
          return false;
        }
      }
    } else {
      for (final SmartString s : my_parameter.values()) {
        if (s.getNullity() == Nullity.NULLABLE) {
          return false;
        }
      }
    }
    return true;
  }
}
