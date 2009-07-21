package freeboogie.vcgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Logger;

import genericutils.*;

import freeboogie.ast.*;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Desugar havoc commands into assignments from fresh variables.
 *
 * The code
 * <pre>
 * implementation I() returns (x : int where P(x)) {
 *   var y : int where Q(x, y);
 * entry:
 *   havoc x;
 *   havoc y;
 * }
 * </pre>
 * becomes
 * <pre>
 * implementation I() returns (x : int where P(x)) {
 *   var x$fresh : int;
 *   var y$fresh : int;
 *   var y where Q(x, y);
 * entry:
 *   x := x$fresh; assume P(x$fresh);
 *   y := y$fresh; assume Q(x, y$fresh);
 * }
 * </pre>
 *
 * Note that the place of the assume commands is relevant since
 * the program is not yet passive. A subsequent phase will get rid
 * of the other <b>where</b> clauses.
 *
 * TODO This is a bit too similar to call desugarer. Try to factor out code.
 *
 * @see freeboogie.vcgen.VcGenerator
 */
public class HavocDesugarer extends Transformer {
  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private ArrayList<Command> equivCmds;
  private HashMap<VariableDecl, AtomId> toSubstitute;
  private Declaration newVars;

  public HavocDesugarer() {
    equivCmds = new ArrayList<Command>(23);
    toSubstitute = new HashMap<VariableDecl, AtomId>(23);
  }

  // === transformer methods ===
  @Override
  public Body eval(Body body, Declaration vars, Block blocks) {
    newVars = vars;
    Block newBlocks = blocks == null? null : (Block)blocks.eval(this);
    if (newVars != vars || newBlocks != blocks)
      body = Body.mk(newVars, newBlocks, body.loc());
    return body;
  }

  @Override
  public Block eval(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    Block newTail = tail == null? null : (Block)tail.eval(this);
    equivCmds.clear();
    Command newCmd = cmd == null? null : (Command)cmd.eval(this);
    if (!equivCmds.isEmpty()) {
      String crtLabel, nxtLabel;
      block = Block.mk(nxtLabel = Id.get("havoc"), null, succ, newTail, block.loc());
      for (int i = equivCmds.size() - 1; i > 0; --i) {
        block = Block.mk(
          crtLabel = Id.get("havoc"),
          equivCmds.get(i),
          Identifiers.mk(AtomId.mk(nxtLabel, null), null),
          block,
          block.loc());
        nxtLabel = crtLabel;
      }
      block = Block.mk(
        name,
        equivCmds.get(0),
        Identifiers.mk(AtomId.mk(nxtLabel, null), null),
        block,
        block.loc());
    } else if (newTail != tail || newCmd != cmd)
      block = Block.mk(name, newCmd, succ, newTail);
    return block;
  }

  @Override
  public HavocCmd eval(HavocCmd havocCmd, Identifiers ids) {
    toSubstitute.clear();
    Expr e = AtomLit.mk(AtomLit.AtomType.TRUE, havocCmd.loc());
    while (ids != null) {
      VariableDecl vd = (VariableDecl)tc.getST().ids.def(ids.getId());
      VariableDecl vd2 = tc.getParamMap().def(vd);
      if (vd2 != null) vd = vd2;
      AtomId fresh = AtomId.mk(Id.get("fresh"), null, ids.loc());
      toSubstitute.put(vd, fresh);
      equivCmds.add(AssignmentCmd.mk(ids.getId(), fresh, havocCmd.loc()));
      if (vd.getType() instanceof DepType) {
        Expr p = ((DepType)vd.getType()).getPred();
        e = BinaryOp.mk(BinaryOp.Op.AND, e, (Expr)p.eval(this).clone(), p.loc());
      }
      newVars = VariableDecl.mk(
        null,
        fresh.getId(),
        TypeUtils.stripDep(vd.getType()).clone(),
        vd.getTypeArgs() == null? null : vd.getTypeArgs().clone(),
        newVars);
      ids = ids.getTail();
    }
    equivCmds.add(AssertAssumeCmd.mk(
      AssertAssumeCmd.CmdType.ASSUME,
      null,
      e,
      havocCmd.loc()));
    toSubstitute.clear();
    return null;
  }

  @Override
  public AtomId eval(AtomId atomId, String id, TupleType types) {
    Declaration d = tc.getST().ids.def(atomId);
    AtomId r = toSubstitute.get(d);
    return r == null? atomId : r.clone();
  }

 
}

