package b2bpl.bpl.ast;


public abstract class BPLCommand extends BPLNode {

  public static final BPLCommand[] EMPTY_ARRAY = new BPLCommand[0];

  public abstract boolean isPassive();
}
