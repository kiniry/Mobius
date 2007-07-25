package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.bml.ast.BMLAssertStatement;
import b2bpl.bytecode.bml.ast.BMLPredicate;


public class AssertAttribute extends Attribute {

  public static final String NAME = "Assert";

  private final Label[] labels;

  private final BMLAssertStatement[] assertions;

  public AssertAttribute() {
    this(null, null);
  }

  public AssertAttribute(Label[] labels, BMLAssertStatement[] assertions) {
    super(NAME);
    this.labels = labels;
    this.assertions = assertions;
  }

  /** {@inheritDoc} */
  public Label[] getLabels() {
    return labels;
  }

  public BMLAssertStatement[] getAssertions() {
    return assertions;
  }

  /** {@inheritDoc} */
  public boolean isCodeAttribute() {
    return true;
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

    int assertionCount = reader.readShort();
    Label[] assertionLabels = new Label[assertionCount];
    BMLAssertStatement[] assertions = new BMLAssertStatement[assertionCount];
    for (int i = 0; i < assertionCount; i++) {
      int bcIndex = reader.readShort();
      assertionLabels[i] = getLabel(bcIndex, labels);
      BMLPredicate predicate = reader.readPredicate();
      assertions[i] = new BMLAssertStatement(predicate);
    }

    return new AssertAttribute(assertionLabels, assertions);
  }

  private static Label getLabel(int index, Label[] labels) {
    if (labels[index] == null) {
      labels[index] = new Label();
    }
    return labels[index];
  }

  /** {@inheritDoc} */
  protected ByteVector write(
      ClassWriter cw,
      byte[] code,
      int len,
      int maxStack,
      int maxLocals) {
    ByteVector bytes = new ByteVector();
    BMLFlattener flattener = new BMLFlattener(cw, bytes);

    bytes.putShort(assertions.length);
    for (int i = 0; i < assertions.length; i++) {
      bytes.putShort(labels[i].getOffset());
      assertions[i].getPredicate().accept(flattener);
    }

    return bytes;
  }
}
