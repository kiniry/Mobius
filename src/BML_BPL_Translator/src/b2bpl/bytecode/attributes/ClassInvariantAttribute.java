package b2bpl.bytecode.attributes;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.objectweb.asm.Attribute;
import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;

import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.bml.ast.BMLInvariant;
import b2bpl.bytecode.bml.ast.BMLPredicate;


public class ClassInvariantAttribute extends Attribute {

  public static final String NAME = "ClassInvariant";

  private final JClassType owner;

  private final BMLInvariant[] invariants;

  public ClassInvariantAttribute(JClassType owner) {
    super(NAME);
    this.owner = owner;
    this.invariants = null;
  }

  public ClassInvariantAttribute(BMLInvariant[] invariants) {
    super(NAME);
    this.owner = null;
    this.invariants = invariants;
  }

  public BMLInvariant[] getInvariants() {
    return invariants;
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
    BMLInvariant[] invariants = new BMLInvariant[invariantCount];
    for (int i = 0; i < invariantCount; i++) {
      // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
//      int type = reader.readByte();
      BMLPredicate predicate = reader.readPredicate();
      invariants[i] = new BMLInvariant(0, owner, predicate);
    }

    // [SW]: Check admissibility of invariants.
    //       At this point, field references are ONLY allowed to
    //       fields declared within the same class.
    //       Valid invariants:     f >= 0;
    //                             this.a != null;
    //       Invalid invariants:   a.f >= 0;
    //                             this.a.b != null;
    // TODO: this should be replaced by a more sophisticated algorithm,
    //       particularly if the admissibility of invariants changes.
    ClassInvariantAttribute cia = new ClassInvariantAttribute(invariants);
    Pattern pattern = Pattern.compile("^invariant\\s([^\\.]*|this.[^\\.]*)(\\s&&\\s([^\\.]*|this.[^\\.]*))*;$");

    for (BMLInvariant inv : cia.getInvariants()) {
      Matcher matcher = pattern.matcher(inv.toString());
      if (!matcher.find()) 
        System.out.println("COMPILE ERROR: The following invariant is not admissible in " + owner.getName() + ":\n\t" + inv.toString());
    }
    
    return new ClassInvariantAttribute(invariants);
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
    for (BMLInvariant invariant : invariants) {
      // FIXME[om]: This does not correspond to the attribute format of the Mobius project!
//      bytes.putByte(invariant.isStatic() ? 0 : 1);
      invariant.getPredicate().accept(flattener);
    }

    return bytes;
  }
}
