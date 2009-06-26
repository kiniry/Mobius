package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.Field;
import mobius.bmlvcgen.bml.FieldVisitor;

/**
 * Bmllib implementation of Field interface.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
// TODO: How to parse field specs??
public class BmllibField implements Field {
  private final org.apache.bcel.classfile.Field field;
  
  /**
   * Constructor.
   * @param field Bmllib field to be wrapped.
   */
  public BmllibField(
    final org.apache.bcel.classfile.Field field) {
    this.field = field;
  }
  
  /** {@inheritDoc} */
  public void accept(final FieldVisitor v) {
    v.visitFlags(AccessFlag.fromMask(field.getAccessFlags()));
    v.visitName(field.getName());
    v.visitType(BcelType.getInstance(field.getType()));
  }
  
}
