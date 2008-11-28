/**
 * 
 */
package annot.attributes;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Visitor;

import annot.bcclass.BCClass;
import annot.bcclass.BCClassRepresentation;
import annot.io.AttributeWriter;
import annot.textio.DisplayStyle;

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
    return this.bcc.getCp().findConstant(DisplayStyle.FIELD_MODIFIERS_ATTR);
  }

  public String getName() {
    return DisplayStyle.FIELD_MODIFIERS_ATTR;
  }

  public void save(AttributeWriter aw) {
    aw.writeInt(modifiers);
  }


}
