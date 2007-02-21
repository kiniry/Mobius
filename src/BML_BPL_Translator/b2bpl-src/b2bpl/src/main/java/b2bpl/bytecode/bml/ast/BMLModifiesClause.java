package b2bpl.bytecode.bml.ast;


public class BMLModifiesClause extends BMLSpecificationClause {

  private final BMLStoreRef[] storeRefs;

  public BMLModifiesClause(BMLStoreRef... storeRefs) {
    this.storeRefs = storeRefs;
  }

  public BMLStoreRef[] getStoreRefs() {
    return storeRefs;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("modifies ");
    for (int i = 0; i < storeRefs.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(storeRefs[i]);
    }
    sb.append(";");

    return sb.toString();
  }
}
