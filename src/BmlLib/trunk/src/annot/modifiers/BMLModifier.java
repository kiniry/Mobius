/**
 * 
 */
package annot.modifiers;


import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.BMLModifierAttribute;
import annot.bcclass.BCClassRepresentation;
import annot.bcclass.BMLModifiersFlags;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.DisplayStyle;

/**
 * @author alx
 *
 */
public class BMLModifier {

  private int modifiers;
  private boolean isRead;
  private BCClassRepresentation bcc;

  public BMLModifier(Field afield,
                     BCClassRepresentation classRepresentation)
    throws ReadAttributeException {
    bcc = classRepresentation;
    readModifiers(afield.getAttributes());
  }
  /**
   *  
   * @param attributes
   * @throws ReadAttributeException - if given attribute's
   *     data doesn't represent correct attribute of
   *     given attribute's name.
   */
  private void readModifiers(Attribute[] attributes)
    throws ReadAttributeException {
    AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i < attributes.length; i++) {
      if (attributes[i] instanceof Unknown) {
        Unknown new_name = (Unknown) attributes[i];
        ar.readAttribute(new_name);
        if (isRead) return;
      }
    }
    return;
  }

  public void load(AttributeReader ar) throws ReadAttributeException {
    modifiers = ar.readInt();
    isRead = true;
  }

  public BMLModifierAttribute getAttribute() {
    return new BMLModifierAttribute(bcc, modifiers);
  }

  /**
   * Displays content of the current modifiers. We assume that the array
   * {@link BMLModifiersFlags#BML_MODIFIERS} is in sync with the array
   * {@link DisplayStyle}{@link #BML_MODIFIERS}.
   *
   * @return String representation of the current modifiers
   */
  @Override
  public String toString() {
    return printBMLModifiers(modifiers);
  }

  /**
   * Displays content of the current modifiers. We assume that the array
   * {@link BMLModifiersFlags#BML_MODIFIERS} is in sync with the array
   * {@link DisplayStyle}{@link #BML_MODIFIERS}.
   *
   * @param modifiers the modifiers to print out
   * @return String representation of the current modifiers
   */
  public static String printBMLModifiers(final int modifiers) {
    final StringBuffer buf = new StringBuffer("");
    for (int i = 0; i < BMLModifiersFlags.BML_MODIFIERS.length; i++) {
      if ((modifiers & BMLModifiersFlags.BML_MODIFIERS[i]) != 0) {
        if (buf.length() > 0) {
          buf.append(" ");
        }
        buf.append(DisplayStyle.BML_MODIFIERS[i]);
      }
    }
    return buf.toString();
  }
}
