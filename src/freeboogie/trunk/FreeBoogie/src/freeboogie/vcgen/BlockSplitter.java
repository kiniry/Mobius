package freeboogie.vcgen;

import freeboogie.ast.*;
import freeboogie.util.Id;

/**
 * Chops blocks so that each contains at most one command.
 * Use it using the eval function (see {@code Transfomer}).
 *
 * @author rgrig
 * @author miko
 */
public class BlockSplitter extends Transformer {
  private String origName;

  private Block blockFromCmds(
    String name, Commands cmds, Identifiers succ, Block tail
  ) {
    if (cmds.getTail() != null) {
      String nname = Id.get(origName);
      tail = blockFromCmds(nname, cmds.getTail(), succ, tail);
      succ = Identifiers.mk(AtomId.mk(nname), null);
    }
    cmds = Commands.mk(cmds.getCmd(), null);
    return Block.mk(name, cmds, succ, tail);
  }

  @Override
  public Block eval(Block block, String name, Commands cmds, Identifiers succ, Block tail) {
    if (tail != null) tail = (Block)tail.eval(this);
    if (cmds == null) return Block.mk(name, null, succ, tail);
    origName = name;
    return blockFromCmds(name, cmds, succ, tail);
  }
}
