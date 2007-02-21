package b2bpl.bytecode.attributes;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.ast.BMLEnsuresClause;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLExsuresClause;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.bml.ast.BMLModifiesClause;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLRequiresClause;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;
import b2bpl.bytecode.bml.ast.BMLStoreRef;


public class MethodSpecificationAttribute extends Attribute {

  public static final String NAME = "MethodSpecification";

  private final BMLMethodSpecification specification;

  public MethodSpecificationAttribute() {
    this(null);
  }

  public MethodSpecificationAttribute(BMLMethodSpecification specification) {
    super(NAME);
    this.specification = specification;
  }

  public BMLMethodSpecification getSpecification() {
    return specification;
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

    BMLPredicate predicate = reader.readPredicate();
    BMLRequiresClause requires = new BMLRequiresClause(predicate);

    int specCount = reader.readShort();
    BMLSpecificationCase[] specCases = new BMLSpecificationCase[specCount];
    for (int i = 0; i < specCount; i++) {
      specCases[i] = readSpecificationCase(reader);
    }

    BMLMethodSpecification specification =
      new BMLMethodSpecification(requires, specCases);

    return new MethodSpecificationAttribute(specification);
  }

  private static BMLSpecificationCase readSpecificationCase(
      BMLAttributeReader reader) {
    BMLPredicate requiresPredicate = reader.readPredicate();
    BMLRequiresClause requires = new BMLRequiresClause(requiresPredicate);

    int modifiesCount = reader.readShort();
    BMLStoreRef[] storeRefs = new BMLStoreRef[modifiesCount];
    for (int i = 0; i < modifiesCount; i++) {
      storeRefs[i] = reader.readStoreRef();
    }
    BMLModifiesClause modifies = new BMLModifiesClause(storeRefs);

    BMLPredicate ensuresPredicate = reader.readPredicate();
    BMLEnsuresClause ensures = new BMLEnsuresClause(ensuresPredicate);

    int exsuresCount = reader.readShort();
    BMLExsuresClause[] exsures = new BMLExsuresClause[exsuresCount];
    for (int i = 0; i < exsuresCount; i++) {
      // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
      reader.readByte();
      JType type = reader.readType();
      BMLPredicate exsuresPredicate = reader.readPredicate();
      exsures[i] = new BMLExsuresClause(type, exsuresPredicate);
    }

    return new BMLSpecificationCase(requires, modifies, ensures, exsures);
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

    specification.getRequires().getPredicate().accept(flattener);
    BMLSpecificationCase[] cases = specification.getCases();
    bytes.putShort(cases.length);
    for (BMLSpecificationCase specCase : cases) {
      BMLExpression pre = specCase.getRequires().getPredicate();
      pre.accept(flattener);
      BMLStoreRef[] storeRefs = specCase.getModifies().getStoreRefs();
      bytes.putShort(storeRefs.length);
      for (BMLStoreRef storeRef : storeRefs) {
        storeRef.accept(flattener);
      }
      BMLExpression post = specCase.getEnsures().getPredicate();
      post.accept(flattener);
      BMLExsuresClause[] exsures = specCase.getExsures();
      bytes.putShort(exsures.length);
      for (BMLExsuresClause ex : exsures) {
        // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
        bytes.putByte(BMLAttributeTags.JAVA_TYPE);
        bytes.putShort(cw.newClass(ex.getExceptionType().getInternalName()));
        ex.getPredicate().accept(flattener);
      }
    }

    return bytes;
  }
}
