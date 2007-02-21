package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.bml.ast.BMLAssumeStatement;
import b2bpl.bytecode.bml.ast.BMLPredicate;


public class AssumeAttribute extends Attribute {

  public static final String NAME = "Assume";

  private final Label[] labels;

  private final BMLAssumeStatement[] assumptions;

  public AssumeAttribute() {
    this(null, null);
  }

  public AssumeAttribute(Label[] labels, BMLAssumeStatement[] assumptions) {
    super(NAME);
    this.labels = labels;
    this.assumptions = assumptions;
  }

  /** {@inheritDoc} */
  public Label[] getLabels() {
    return labels;
  }

  public BMLAssumeStatement[] getAssumptions() {
    return assumptions;
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

    int assumptionCount = reader.readShort();
    Label[] assumptionLabels = new Label[assumptionCount];
    BMLAssumeStatement[] assumptions = new BMLAssumeStatement[assumptionCount];
    for (int i = 0; i < assumptionCount; i++) {
      int bcIndex = reader.readShort();
      assumptionLabels[i] = getLabel(bcIndex, labels);
      BMLPredicate predicate = reader.readPredicate();
      assumptions[i] = new BMLAssumeStatement(predicate);
    }

    return new AssumeAttribute(assumptionLabels, assumptions);
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

    bytes.putShort(assumptions.length);
    for (int i = 0; i < assumptions.length; i++) {
      bytes.putShort(labels[i].getOffset());
      assumptions[i].getPredicate().accept(flattener);
    }

    return bytes;
  }
}
