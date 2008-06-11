package freeboogie.tc;

import java.util.*;
import freeboogie.ast.*;
import freeboogie.util.StackedHashMap;

// for debug
import java.io.PrintWriter;
import freeboogie.astutil.PrettyPrinter;

@SuppressWarnings("serial")
class UnknownSpecialization extends Exception {}

/**
 * Makes sure that all (eligible) IDs have explicit specializations
 * attached. The information used to achieve this consists of
 * (1) errors: a map from expressions to the AtomId in the type
 * variable declaration to which the expresion type evaluated
 * &mdash; this can be easily derived from the errors of type
 * REQ_SPECIALIZATION provided by {@code TypeChecker}, 
 * (2) desired: a map from expressions to their desired types
 * &mdash; this can be provided by {@code Inferrer}, and
 * (3) implicit: the implicit specializations identified
 * by the {@code TypeChecker} &mdash; these need to be 'folded'.
 *
 * A symbol table for the input AST is needed to so that declarations
 * of identifiers (which may need specialisation) can be quickly
 * looked up.
 *
 * @see freeboogie.tc.TypeChecker
 *
 * TODO There is too much similar code around here. Try to refactor.
 */
public class Specializer extends Transformer {

  // used to look up variable, functions, and procedures
  private SymbolTable st;

  // errors.get(x) is the (declaration of) the type variable that
  // corresponds to x; of course, the type should be a type, not
  // a type variable, so that's why these are 'errors'
  private Map<Expr, AtomId> errors;

  // desired types for various nodes
  private Map<Expr, Type> desired;

  // the specializations found by the type-checker
  private Map<Ast, Map<AtomId, Type>> implicit;

  // used to 'collate' specializations found by the typechecker
  private StackedHashMap<AtomId, Type> specialisations;

  // === public interface ===
  
  /**
   * Introduce explicit specialisations in {@code ast}.
   *
   * @param ast the program in which to introduce explicit specializations
   * @param st a symbol table that knows symbols in {@code ast}
   * @param errors maps expressions to type variable declarations
   *            (they are 'errors' because expressions should have
   *            'real' types)
   * @param desired maps expressions to a gues of what their type should be
   *            (NOTE: This might also be a type variable, that should
   *            be introduced as a generic later on)
   * @param implicit contains the type parameters identified by
   *            {@code TypeChecker}
   */
  public Declaration process(
    Declaration ast, 
    SymbolTable st,
    Map<Expr, AtomId> errors,
    Map<Expr, Type> desired,
    Map<Ast, Map<AtomId, Type>> implicit
  ) {
    this.st = st;
    this.errors = errors;
    this.desired = desired;
    this.implicit = implicit;
    specialisations = new StackedHashMap<AtomId, Type>();

    for (Expr e : errors.keySet()) assert desired.containsKey(e);

    return (Declaration)ast.eval(this);
  }

  // === workers ===
  
  @Override
  public void enterNode(Ast n) {
    Map<AtomId, Type> is = implicit.get(n);
    AtomId ai = n instanceof Expr ? errors.get((Expr)n) : null;
    if (is != null || ai != null) {
      //System.out.println("PUSH AT " + n.loc());
      specialisations.push();
    }
    if (is != null) {
      //for (Map.Entry<AtomId, Type> e : is.entrySet())
      //  System.out.println("add: " + e.getKey().getId() + "->" + TypeUtils.typeToString(e.getValue()));
      specialisations.putAll(is);
    }
    if (ai != null) {
      //System.out.println("add: " + ai.getId() + "->" + TypeUtils.typeToString(desired.get((Expr)n)));
      specialisations.put(ai, desired.get((Expr)n));
    }
  }

  @Override
  public void exitNode(Ast n) {
    if (implicit.containsKey(n) || (n instanceof Expr && errors.containsKey((Expr)n))) {
      //System.out.println("POP AT " + n.loc());
      specialisations.pop();
    }
  }

  @Override
  public AtomId eval(AtomId atomId, String id, TupleType types) {
    Declaration d = st.ids.def(atomId);
    if (!(d instanceof VariableDecl)) return atomId;
    VariableDecl vd = (VariableDecl)d;
    try {
      types = prepareTypeList(vd.getTypeVars());
    } catch (UnknownSpecialization e) {
      return atomId;
    }
    return AtomId.mk(id, types, atomId.loc());
  }

  @Override
  public AtomFun eval(AtomFun atomFun, String function, TupleType types, Exprs args) {
    if (args != null) args = (Exprs)args.eval(this);
    Signature sig = st.funcs.def(atomFun).getSig();
    try { 
      types = prepareTypeList(sig.getTypeVars());
    } catch (UnknownSpecialization e) {}
    return AtomFun.mk(function, types, args, atomFun.loc());
  }

  @Override
  public CallCmd eval(CallCmd callCmd, String procedure, TupleType types, Identifiers results, Exprs args) {
    if (results != null) results = (Identifiers)results.eval(this);
    if (args != null) args = (Exprs)args.eval(this);
    Signature sig = st.procs.def(callCmd).getSig();
    try {
      types = prepareTypeList(sig.getTypeVars());
    } catch (UnknownSpecialization e) {}
    return CallCmd.mk(procedure, types, results, args);
  }

  
  // === helpers ===

  private TupleType prepareTypeList(Identifiers ids) 
  throws UnknownSpecialization {
    if (ids == null) return null;
    AtomId ai = ids.getId();
    Type t = specialisations.get(ai);
    if (t == null) throw new UnknownSpecialization();
    return TupleType.mk(t, prepareTypeList(ids.getTail()));
  }

}
