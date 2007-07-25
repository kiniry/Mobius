package b2bpl.bytecode.bml.ast;

import b2bpl.bytecode.BCMember;
import b2bpl.bytecode.JClassType;


public class BMLConstraint extends BCMember {

  public static final BMLConstraint[] EMPTY_ARRAY = new BMLConstraint[0];

  private final BMLPredicate predicate;

  public BMLConstraint(
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
    return "constraint " + predicate + ";";
  }
}
