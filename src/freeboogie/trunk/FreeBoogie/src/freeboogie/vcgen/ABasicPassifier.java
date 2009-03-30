package freeboogie.vcgen;

import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.AtomId;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
import freeboogie.ast.Transformer;
import freeboogie.ast.VariableDecl;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

public abstract class ABasicPassifier extends Transformer {

  private final TcInterface fTypeChecker;
  private boolean fIsVerbose;
  public ABasicPassifier (TcInterface tc, boolean bVerbose) {
    fTypeChecker = tc;
    fIsVerbose = bVerbose;
  }
  /**
   * Returns the variable declaration corresponding to the given id.
   * @param id the id to check for
   * @return a valid variable declaration or null
   */
  VariableDecl getDeclaration(AtomId id) {
    Declaration decl = getTypeChecker().getST().ids.def(id);
    if (decl instanceof VariableDecl) {
      return (VariableDecl) decl;
    }
    return null;
  }
  public TcInterface getTypeChecker() {
    return fTypeChecker;
  }  
  
  public static AssertAssumeCmd mkAssumeEQ(Expr left, Expr right) {
    return AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
      BinaryOp.mk(BinaryOp.Op.EQ, left, right));
  }
  
  public static AtomId mkVar(VariableDecl decl, int idx) {
    String name = decl.getName();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return AtomId.mk(name, null);
  }
  
  public static AtomId mkVar(AtomId id, int idx) {
    String name = id.getId();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return  AtomId.mk(name, id.getTypes(), id.loc());
  }
  
  public static VariableDecl mkDecl(VariableDecl old, int idx, Declaration next) {
    String name = old.getName();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return VariableDecl.mk(
      name,
      TypeUtils.stripDep(old.getType()).clone(),
      old.getTypeVars() == null? null :old.getTypeVars().clone(),
      next);
  }

  public boolean isVerbose() {
    return fIsVerbose;
  }

}