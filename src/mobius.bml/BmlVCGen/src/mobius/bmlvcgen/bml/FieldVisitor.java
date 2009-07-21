package mobius.bmlvcgen.bml;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.Field.AccessFlag;
import mobius.bmlvcgen.bml.types.Type;

/**
 * Interface of objects used to visit fields.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface FieldVisitor {
  /**
   * Visit access flags.
   * @param flags Access flags.
   */
  void visitFlags(EnumSet<AccessFlag> flags);
  
  /**
   * Visit field name.
   * @param name Name.
   */
  void visitName(String name);
  
  /**
   * Visit field type.
   * @param t Type.
   */
  void visitType(Type t);
}
