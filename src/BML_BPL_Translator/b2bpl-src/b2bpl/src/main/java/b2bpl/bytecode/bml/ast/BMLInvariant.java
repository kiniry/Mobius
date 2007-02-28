package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.BCMember;
import b2bpl.bytecode.JClassType;


public class BMLInvariant extends BCMember {

  public static final BMLInvariant[] EMPTY_ARRAY = new BMLInvariant[0];

  private final BMLPredicate predicate;

  public BMLInvariant(
      int accessModifiers,
      JClassType owner,
      BMLPredicate predicate) {
    super(accessModifiers, owner);
    this.predicate = predicate;
  }

  public BMLPredicate getPredicate() {
    return predicate;
  }

  public String toString() {
    return "invariant " + predicate + ";";
  }
}
