package freeboogie.tc;

import java.util.*;

import freeboogie.ast.*;

/**
 * Checks whether the implementations' signatures correspond
 * to the procedure signatures. It also connects in/out {@code
 * VariableDecl} arguments of the implementation with the one in
 * the procedure. (This link is needed later when verifying that
 * the implementation satisfies the spec that accompanies the
 * procedure.) It produces errors if an implementation does not
 * have a corresponding procedure or if there is a type mismatch
 * in the signature.
 *
 * @author rgrig 
 */
@SuppressWarnings("unused") // unused parameters
public class ImplementationChecker extends Transformer {
  private List<FbError> errors;
  private GlobalsCollector gc;
  
  // connects implementations to procedures
  private UsageToDefMap<Implementation, Procedure> implProc;
  
  // connects implementation parameters to procedure parameters
  private UsageToDefMap<VariableDecl, VariableDecl> paramMap;
  
  // === public interface ===
  
  /**
   * Processes the implementations in {@code ast} assuming that {@code p}
   * maps procedure names to their AST nodes. ({@code GlobalsCollector} provides
   * such a mapping.)
   * @param ast the AST to check
   * @param g the globals collector that can resolve procedure names 
   * @return the detected problems 
   */
  public List<FbError> process(Declaration ast, GlobalsCollector g) {
    errors = new ArrayList<FbError>();
    gc = g;
    implProc = new UsageToDefMap<Implementation, Procedure>();
    paramMap = new UsageToDefMap<VariableDecl, VariableDecl>();
    ast.eval(this);
    return errors;
  }
  
  /**
   * Returns the map linking procedures to their usages.
   * @return the map linking procedures to their usages
   */
  public UsageToDefMap<Implementation, Procedure> getImplProc() {
    return implProc;
  }
  
  /**
   * Returns the map of implementation in/out parameters to the map
   * of procedure in/out parameters.
   * @return the link between implementation and procedure parameters
   */
  public UsageToDefMap<VariableDecl, VariableDecl> getParamMap() {
    return paramMap;
  }
  
  // === helpers ==
  
  // assumes {@code a} and {@code b} are lists of {@code VariableDecl}
  // compares their types and connects them in implDecl
  // reports type mismatches
  private void compare(Declaration a, Declaration b) {
    if (a == null && b == null) return;
    if (a == null ^ b == null) {
      errors.add(new FbError(FbError.Type.IP_CNT_MISMATCH, a==null? b:a));
      return;
    }
    
    VariableDecl va = (VariableDecl)a;
    VariableDecl vb = (VariableDecl)b;
    if (!TypeUtils.eq(TypeUtils.stripDep(va.getType()), TypeUtils.stripDep(vb.getType()))) {
      errors.add(new FbError(FbError.Type.EXACT_TYPE, va,
            TypeUtils.typeToString(vb.getType())));
      return;
    }
    paramMap.put(va, vb);
    compare(va.getTail(), vb.getTail());
  }
  
  // assumes {@code a} and {@code b} are lists of {@code VariableDecl}
  // checks that a does not have dependent types
  private void depCheck(Declaration a) {
    if (a == null) return;
    VariableDecl va = (VariableDecl)a;
    if (TypeUtils.hasDep(va.getType()))
      errors.add(new FbError(FbError.Type.DEP_IMPL_SIG, va));
  }
  
  // === visiting implementations ===

  @Override
  public void see(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    String name = sig.getName();
    Procedure p = gc.procDef(name);
    if (p == null) {
      errors.add(new FbError(FbError.Type.PROC_MISSING, implementation));
      return;
    }
    
    implProc.put(implementation, p);
    
    Signature psig = p.getSig();
    compare(sig.getArgs(), psig.getArgs());
    compare(sig.getResults(), psig.getResults());
    
    depCheck(sig.getArgs());
    depCheck(sig.getResults());

    if (tail != null) tail.eval(this);
  }
}
