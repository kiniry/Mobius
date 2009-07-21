package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLLoopInvariant;
import b2bpl.bytecode.bml.ast.BMLLoopModifiesClause;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.bml.ast.BMLLoopVariant;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLStoreRef;


public class LoopSpecificationAttribute extends Attribute {

  public static final String NAME = "LoopSpecification";

  private final Label[] labels;

  private final BMLLoopSpecification[] loopSpecifications;

  public LoopSpecificationAttribute() {
    this(null, null);
  }

  public LoopSpecificationAttribute(
      Label[] labels,
      BMLLoopSpecification[] loopSpecifications) {
    super(NAME);
    this.labels = labels;
    this.loopSpecifications = loopSpecifications;
  }

  public Label[] getLabels() {
    return labels;
  }

  public BMLLoopSpecification[] getLoopSpecifications() {
    return loopSpecifications;
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

    int loopCount = reader.readShort();
    Label[] specLabels = new Label[loopCount];
    BMLLoopSpecification[] loopSpecs = new BMLLoopSpecification[loopCount];
    for (int i = 0; i < loopCount; i++) {
      int bcIndex = reader.readShort();
      specLabels[i] = getLabel(bcIndex, labels);

      int modifiesCount = reader.readShort();
      BMLStoreRef[] storeRefs = new BMLStoreRef[modifiesCount];
      for (int j = 0; j < modifiesCount; j++) {
        storeRefs[j] = reader.readStoreRef();
      }
      BMLLoopModifiesClause modifies = new BMLLoopModifiesClause(storeRefs);

      BMLPredicate predicate = reader.readPredicate();
      BMLLoopInvariant invariant = new BMLLoopInvariant(predicate);

      BMLExpression expression = reader.readExpression();
      BMLLoopVariant variant = new BMLLoopVariant(expression);

      loopSpecs[i] = new BMLLoopSpecification(modifies, invariant, variant);
    }

    return new LoopSpecificationAttribute(specLabels, loopSpecs);
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

    bytes.putShort(loopSpecifications.length);
    for (int i = 0; i < loopSpecifications.length; i++) {
      BMLLoopSpecification loopSpec = loopSpecifications[i];
      bytes.putShort(labels[i].getOffset());
      BMLLoopModifiesClause modifies = loopSpec.getModifies();
      BMLStoreRef[] storeRefs = modifies.getStoreRefs();
      bytes.putShort(storeRefs.length);
      for (BMLStoreRef storeRef : storeRefs) {
        storeRef.accept(flattener);
      }
      loopSpec.getInvariant().getPredicate().accept(flattener);
      loopSpec.getVariant().getExpression().accept(flattener);
    }

    return bytes;
  }
}
