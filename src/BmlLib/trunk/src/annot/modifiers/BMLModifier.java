/**
 * 
 */
package annot.modifiers;

import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.BMLModifierAttribute;
import annot.attributes.SpecificationCase;
import annot.bcclass.BCClassRepresentation;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * @author alx
 *
 */
public class BMLModifier {

  private int modifiers;
  private boolean isRead;
  private BCClassRepresentation bcc;

  public BMLModifier(Field afield,
                     BCClassRepresentation classRepresentation) throws ReadAttributeException {
    bcc = classRepresentation;
    readModifiers(afield.getAttributes());
  }

  private void readModifiers(Attribute[] attributes) throws ReadAttributeException {
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

}
