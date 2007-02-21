package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.bml.ast.BMLConstraint;
import b2bpl.bytecode.bml.ast.BMLPredicate;


public class ConstraintAttribute extends Attribute {

  public static final String NAME = "Constraint";

  private final JClassType owner;

  private final BMLConstraint[] constraints;

  public ConstraintAttribute(JClassType owner) {
    super(NAME);
    this.owner = owner;
    this.constraints = null;
  }

  public ConstraintAttribute(BMLConstraint[] constraints) {
    super(NAME);
    this.owner = null;
    this.constraints = constraints;
  }

  public BMLConstraint[] getConstraints() {
    return constraints;
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

    // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
    int invariantCount = 1;//reader.readShort();
    BMLConstraint[] constraints = new BMLConstraint[invariantCount];
    for (int i = 0; i < invariantCount; i++) {
      // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
//      int type = reader.readByte();
      BMLPredicate predicate = reader.readPredicate();
      constraints[i] = new BMLConstraint(0, owner, predicate);
    }

    return new ConstraintAttribute(constraints);
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

    // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
//    bytes.putShort(invariants.length);
    for (BMLConstraint constraint : constraints) {
      // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
//      bytes.putByte(invariant.isStatic() ? 0 : 1);
      constraint.getPredicate().accept(flattener);
    }

    return bytes;
  }
}
