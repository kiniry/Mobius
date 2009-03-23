/**
 * 
 */
package annot.attributes;

import annot.bcclass.BCClassRepresentation;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.AttributeNames;

/**
 * @author alx
 *
 */
public class BMLModifierAttribute implements IBCAttribute {

  private BCClassRepresentation bcc;
  private int modifiers;

  public BMLModifierAttribute(BCClassRepresentation abcc, int amodifiers) {
    bcc = abcc;
    modifiers = amodifiers;
  }

  public int getIndex() {
    return this.bcc.getCp().findConstant(AttributeNames.FIELD_MODIFIERS_ATTR);
  }

  public String getName() {
    return AttributeNames.FIELD_MODIFIERS_ATTR;
  }

  public void save(AttributeWriter aw) {
    aw.writeInt(modifiers);
  }

  public void load(AttributeReader ar) throws ReadAttributeException {
    // TODO Auto-generated method stub
    
  }


}
