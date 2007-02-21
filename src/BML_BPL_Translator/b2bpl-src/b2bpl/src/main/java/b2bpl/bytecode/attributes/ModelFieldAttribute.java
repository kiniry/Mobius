package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JType;


public class ModelFieldAttribute extends Attribute {

  public static final String NAME = "ModelField";

  private final JClassType owner;

  private final BCField[] fields;

  public ModelFieldAttribute(JClassType owner) {
    super(NAME);
    this.owner = owner;
    fields = null;
  }

  public ModelFieldAttribute(BCField... fields) {
    super(NAME);
    owner = null;
    this.fields = fields;
  }

  public BCField[] getFields() {
    return fields;
  }

  /** {@inheritDoc} */
  public boolean isCodeAttribute() {
    return false;
  }

  /** {@inheritDoc} */
  protected Attribute read(
      ClassReader cr,
      int off,
      int len,
      char[] buf,
      int codeOff,
      Label[] labels) {
    BMLAttributeReader reader = new BMLAttributeReader(cr, off, len, buf);

    int fieldCount = reader.readShort();
    BCField[] fields = new BCField[fieldCount];
    for (int i = 0; i < fieldCount; i++) {
      int accessModifiers = reader.readShort();
      String name = reader.readString();
      JType fieldType = reader.readType();
      fields[i] = new BCField(accessModifiers, owner, name, fieldType, true);
    }

    return new ModelFieldAttribute(fields);
  }

  /** {@inheritDoc} */
  protected ByteVector write(
      ClassWriter cw,
      byte[] code,
      int len,
      int maxStack,
      int maxLocals) {
    ByteVector bytes = new ByteVector();
    bytes.putShort(fields.length);
    for (BCField field : fields) {
      bytes.putShort(field.getAccessModifiers());
      bytes.putShort(cw.newUTF8(field.getName()));
      bytes.putShort(cw.newUTF8(field.getType().getInternalName()));
    }
    return bytes;
  }
}
