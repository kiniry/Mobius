/*
 * Created on Jan 8, 2005
 *
 */
package escjava.translate;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;

import javafe.ast.ASTNode;
import javafe.ast.ArrayRefExpr;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.Identifier;
import javafe.ast.LiteralExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.RoutineDecl;
import javafe.ast.ThisExpr;
import javafe.ast.Type;
import javafe.ast.TypeObjectDesignator;
import javafe.ast.VariableAccess;
import javafe.tc.EnvForTypeSig;
import javafe.tc.TypeSig;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.Main;
import escjava.ast.ArrayRangeRefExpr;
import escjava.ast.CondExprModifierPragmaVec;
import escjava.ast.EverythingExpr;
import escjava.ast.Modifiers;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.ModifiesGroupPragmaVec;
import escjava.ast.NaryExpr;
import escjava.ast.NothingExpr;
import escjava.ast.TagConstants;
import escjava.ast.WildRefExpr;
import escjava.tc.Datagroups;
import escjava.tc.FlowInsensitiveChecks;
import escjava.tc.TypeCheck;
import escjava.tc.Types;


/**
 * @author David Cok
 *
 * This class contains methods for handling frame conditions.
 * <p>
 * Note the following about the implementation of Modifies Pragmas.
 * The desugared frame specifications of a method are contained in a
 * ModifiesGroupPragmaVec, which is a vector of ModifiesGroupPragma elements.
 * Each ModifiesGroupPragma instance corresponds to the frame conditions for
 * a single specification case.  Since each specification case of a method
 * must be independently satisfied, each ModifiesGroupPragma must be 
 * satisfied.
 * <p>
 * A ModifiesGroupPragma contains a precondition (the Expr <obj>.precondition)
 * and a set of CondExprModifierPragma elements in a CondExprModifierPragmaVec.
 * Each CondExprModifierPragma corresponds to one store-ref location as might
 * be listed in an assignable clause (e.g. a field, an array reference, 
 * wild-card items such as obj.* or array[*], array ranges such as array[i..j]).
 * The Expr that is in a CondExprModifierPragma is obsolete. [It used to be
 * that an assignable clause had an optional conditional expression, but that
 * has been deprecated.] The list of store-refs in a ModifierGroupPragma is
 * essentially a union - within a specification case a specifier can list 
 * multiple store-ref locations that may be assigned.  A particular assignment
 * statement will have a lhs which must match one of the store-ref locations
 * in the ModifiesGroup Pragma, and must do so for each ModifiesGroupPragma
 * in the ModifiesGroupPragmaVec.
 * <p>
 * 
 */
public class Frame {
  
  /** The Translate instance that owns this instance of Frame */
  final private Translate translator;
  
  /** The value of issueCautions obtained from the Translate owner */
  final private boolean issueCautions;
  
  /** The RoutineDecl whose body is in the process of being translated */
  final private RoutineDecl rdCurrent;
  
  /** The mapping to be used for \old variables to get pre-state values */
  final private Hashtable premap;
  
  /** This holds a value across recursive invocations of methods
   * within this class; it designates that the object whose field
   * is being assigned is known to be fresh.
   */
  private boolean pFreshResult = false;
  
  /** A precomputed Identifier for 'this', to be used in constructing
   *  Expressions.
   */
  static private final Identifier thisId = Identifier.intern("this");
  
  /** The constructor of a Frame instance; should be called only from
   *  Translate
   * @param t The instance of Translate to which this Frame belongs
   * @param issueCautions Whether to issue Caution messages to the user
   * @param rdCurrent The RoutineDecl whose body is being translated
   * @param premap The mapping to pre-state values to be used in translation
   */
  public Frame(Translate t, boolean issueCautions, RoutineDecl rdCurrent,
      Hashtable premap) {
    translator = t; 
    this.issueCautions = issueCautions;
    this.rdCurrent = rdCurrent;
    this.premap = premap;
  }
  
  // These fields are used in the course of generating checks
  
  /** The kind of expression being checked, e.g. assignment or method call.
   *  Used in the message displayed to the user when the check fails.
   */
  private String kindOfModCheck = "assignment";
  
  /** This method returns whether the given field (fd) of the given object
   * (eod) (which is null if the field is static) is definitely not allowed
   * to be assigned according to the specs of the current RoutineDecl.  By
   * definitely not allowed, we mean that it can be determined without needing
   * to prove the truth or falsity of a given expression.  For example, if
   * the FieldDecl is nowhere mentioned in the ModifiesGroupPragma, then it
   * definitely may not be assigned.  In a situation where the assignable
   * clause contained something like <expr>.field where field matches fd,
   * then the assignment is allowed if <expr> == eod.  But that would have
   * to be proved: it might be that the assignment is not allowed, if 
   * <expr> != eod, but we don't definitely know for sure.
   * @param eod The object whose field is being assigned, or null if the field
   *    is static
   * @param fd The declaration corresponding to the field being assigned.
   * @return
   */
  public boolean isDefinitelyNotAssignable(Expr eod, FieldDecl fd) {
    return modifiesCheckFieldHelper(eod, Location.NULL, fd,
        Location.NULL, null, null, false);
  }
  
  
  /** This method generates checks that the field in lhs is allowed to be
   *  assigned according to the specification of the current RoutineDecl
   *  (rdCurrent).  This may depend on the object whose field is being
   *  assigned.  This is called for both static and instance fields.
   * @param lhs The expression being assigned to (which will be a field
   *              dereference).
   * @param callLoc The location of the field access expression (the lhs).
   * @param fd The location of the declaration of the field being assigned
   */
  void modifiesCheckField(Expr lhs, int callLoc, FieldDecl fd) {
    kindOfModCheck = "assignment";
    // FIXME - I don't think this handles this and super that are not the
    // prefix.
    if (!issueCautions) return;
    // eod is the object part of the FieldAccess, as in an assigment of the
    // form  <eod>.<field> = expr;
    Expr eod = null;
    if (lhs instanceof NaryExpr) {
      eod = (Expr)((NaryExpr)lhs).childAt(2);
    } else if (lhs instanceof VariableAccess) {
      // static field
      // eod stays null
    } else {
      // Unexpected type of lhs - FIXME generate an internal error
      System.out.println("LHS " + lhs.getClass());
      return;
    }
    modifiesCheckFieldHelper(eod,callLoc,fd,Location.NULL,null,null,true);
  }
  
  /** This is a helper method to generate checks that a particular
   * field assignment is allowed by the frame conditions.
   * @param eod The object owning the field being assigned; null if the field
   *              is static
   * @param callLoc The location of the field access being assigned to
   * @param fd   The declaration of the field being assigned to
   * @param calleeLoc The location of the ???, or Location.NULL if there is
   *              no method call involved FIXME
   * @param callee_tpred  ??? FIXME
   * @param callee_tprecondition  ??? FIXME
   * @param addConds  true if the method should generate assertions to be
   *  checked, false if we are just seeing if there are any
   * @return true if there are no assertions to be checked because the
   *   equivalent assertion is equal to 'false'; false if there is one or
   *   more assertion to be checked (only valid if addConds is false).
   */
  private boolean modifiesCheckFieldHelper(Expr eod, int callLoc,
      FieldDecl fd, int calleeLoc, Expr callee_tpred, 
      Expr callee_tprecondition, boolean addConds) {
    boolean notMod = true;
    
    if (!issueCautions && addConds) return false;
    // We need to create a translated predicate expression that is true
    // if the lhs is allowed to be modified and false if it is not
    // allowed to be modified.  This will be an OR across each of the
    // modify pragmas.  Each pragma will contribute
    //   - obviously false if it is not the same declaration or same type
    //   - obviously true if is is the same declaration and both have 'this'
    //  as the od and the condition is true
    //   - obviously true (and then no check) if it is modifies everything
    //  with a true condition
    //   - some expression which is the AND of the condition and that
    //  the lhs matches the modifies expression:
    //      fields must have the same object designator
    //      arrays must have the same array expression and same index
    
    // Loop over each specification case in turn
    ModifiesGroupPragmaVec mg = GetSpec.getCombinedMethodDecl(rdCurrent).modifies;
    for (int kk=0; kk<mg.size(); ++kk) {
      ModifiesGroupPragma mge = mg.elementAt(kk); // The ModifiesGroupPragma
      // for the current specification case
      int callerLoc = mge.clauseLoc;  // Location of one of the modifies 
      // clauses for this specification case
      // ev collects assertions - if any one of them is true then the
      // assignment is allowed; if nothing is in it then it is equivalent
      // to 'false'
      ExprVec ev = ExprVec.make(10);
      if (addConds) {
        // If the field is not a static field, then the assignment is
        // ok if the owning object is fresh since the pre-state.
        if (!Modifiers.isStatic(fd.modifiers)) addAllocExpression(ev,eod);
        if (callee_tpred != null) ev.addElement(GC.not(callee_tpred));
      }
      // Now iterate over all the store-refs in this specification case,
      // including store-refs that are in datagroups - we use this
      // iterator to hide the expansion of the datagroups
      ModifiesIterator caller_iterator = new ModifiesIterator(mge.items,true);
      THISGROUP: while (caller_iterator.hasNext()) {
        Object ex = caller_iterator.next();
        Expr caller_pred = caller_iterator.cond();
        Expr caller_tpred = null;
        if (addConds && !isTrueLiteral(caller_pred)) caller_tpred = 
          modTranslate(caller_pred,true,null);
        if (ex instanceof FieldAccess || ex instanceof FieldDecl) {
          FieldDecl fdd;
          ObjectDesignator odd;
          if (ex instanceof FieldAccess) {
            fdd = ((FieldAccess)ex).decl;
            odd = ((FieldAccess)ex).od;
          } else {
            fdd = (FieldDecl)ex;
            odd = null;
          }
          if (fd == fdd && Modifiers.isStatic(fd.modifiers) == 
            Modifiers.isStatic(fdd.modifiers)) {
            if (Modifiers.isStatic(fd.modifiers)) {
              // Both are static and we already know that they point
              // to the same declaration.  So they match.
              if (addTImplication(ev,callee_tpred,caller_tpred)) { 
                ev = null; break THISGROUP; 
              }
            } else {
              Expr e1 = eod;
              Expr e2 = odd instanceof ExprObjectDesignator ?
                  ((ExprObjectDesignator)odd).expr:
                    ThisExpr.make(null,Location.NULL);
              if ( ((e1 instanceof ThisExpr) || 
                  ((e1 instanceof VariableAccess) && 
                      ((VariableAccess)e1).id == thisId)) && 
                      e2 instanceof ThisExpr && 
                      caller_tpred == null) {
                //System.out.println("TRIVIAL PERMISSION - THIS FIELDS" );
                ev = null;
                break THISGROUP;
              } else {
                ExprVec evv = ExprVec.make(1);
                evv.addElement(e2);
                e1 = eod;
                e2 = modTranslate(e2,true,null);
                Expr e = GC.nary(TagConstants.REFEQ,e1,e2);
                addTImplication(ev,e,callee_tpred,caller_tpred);
              }
            }
          }
        } else if (ex instanceof ArrayRefExpr) {
          // skip
        } else if (ex instanceof NothingExpr) {
          //System.out.println("MATCHING AGAINST NOTHING " );
          // skip
        } else if (ex instanceof EverythingExpr) {
          //System.out.println("MATCHING AGAINST EVERYTHING " );
          if (addTImplication(ev,callee_tpred,caller_tpred)) { ev = null; break THISGROUP; }
          
        } else if (ex instanceof ArrayRangeRefExpr) {
          // skip
        } else if (ex instanceof WildRefExpr) {
          ObjectDesignator odd = ((WildRefExpr)ex).od;
          if (odd instanceof TypeObjectDesignator) {
            if (Modifiers.isStatic(fd.modifiers)) {
              TypeSig t = TypeCheck.inst.getSig(fd.parent);
              Type tt = ((TypeObjectDesignator)odd).type;
              if (t == tt || Types.isSubclassOf(tt,t)) {
                if (addTImplication(ev,callee_tpred,caller_tpred)) { ev = null; break THISGROUP; }
              }
            }
          } else if (odd instanceof ExprObjectDesignator) {
            if (!Modifiers.isStatic(fd.modifiers)) {
              Expr e1 = eod;
              Expr e2 = modTranslate(((ExprObjectDesignator)odd).expr,
                  true,null);
              e1 = GC.nary(TagConstants.REFEQ,e1,e2);
              addTImplication(ev,e1,callee_tpred,caller_tpred);
            }
          } else {
            System.out.println("COMPARE TO " + odd.getClass());
          }
        } else {
          System.out.println("COMPARE TO " + ex.getClass());
        }
      }
      // Two conditions
      // if this method has been called on an assignment, we just have
      //    a callerLoc
      // if the method has been called on a method call, we have a
      //    calleeLoc and a callerLoc and we want the calleeLoc to be
      //    the first associated location
      if (ev != null) {
        notMod = modChecksComplete(mge.precondition,
            callee_tprecondition,ev,callLoc,
            calleeLoc==Location.NULL ? callerLoc : calleeLoc,
                calleeLoc==Location.NULL ? Location.NULL: callerLoc, addConds)
                && notMod;
        //if (!addConds) System.out.println("NOTMOD NOW " + notMod + " " + ev.size());
      } else {
        // definitely modifiable
        //System.out.println("EV IS NULL");
        notMod = false;
      }
    }
    return notMod;
  }
  
  /** This method generates checks that the locations possibly assigned by
   *  a called method are allowed to be assigned by the caller.
   * @param calleeFrameConditions
   * @param eod
   * @param loccall
   * @param args
   * @param freshResult - true if eod is known to be fresh since the prestate
   */
  void modifiesCheckMethodI(ModifiesGroupPragmaVec calleeFrameConditions, 
      Expr eod, int loccall, Hashtable args, boolean freshResult) {
    for (int i=0; i<calleeFrameConditions.size(); ++i) {
      ModifiesGroupPragma mg = calleeFrameConditions.elementAt(i);
      // FIXME - the precondition should not be null - guarding against bugs
      // upstream - e.g. current ArcType, but that may be because of model type problems
      if (mg.precondition == null) {
        //System.out.println("ADDING LIT " + Location.toString(mg.clauseLoc));
        mg.precondition = LiteralExpr.make
        (TagConstants.BOOLEANLIT, Boolean.TRUE, Location.NULL);
        javafe.tc.FlowInsensitiveChecks.setType(mg.precondition,Types.booleanType);
      }
      Expr tp = modTranslate(mg.precondition,false,eod,args);
      modifiesCheckMethod(eod, loccall, mg.items, args, freshResult,tp);
    }
  }
  
  
  //static boolean printreturn = false;
  
  private void modifiesCheckMethod(Expr eod, int loccall, 
      CondExprModifierPragmaVec mp, Hashtable args, boolean freshResult, 
      Expr callee_tprecondition) {
    kindOfModCheck = "method call";
    pFreshResult = freshResult;
    try {
      if (!issueCautions) return;
      ModifiesGroupPragmaVec mg = GetSpec.getCombinedMethodDecl(rdCurrent).modifies;
      for (int kk=0; kk<mg.size(); ++kk) {
        ModifiesGroupPragma mge = mg.elementAt(kk);
        int callerLoc = mge.getStartLoc();
        ModifiesIterator caller_iterator = new ModifiesIterator(mge.items,true);
        ModifiesIterator callee_iterator = new ModifiesIterator(mp,false);
        OUTER: while (callee_iterator.hasNext()) {
          ExprVec ev = ExprVec.make(10);
          Object ex = callee_iterator.next();
          int calleeLoc = ((ASTNode)ex).getStartLoc();
          Expr callee_pred = callee_iterator.cond();
          Expr callee_tpred = null;
          if (!isTrueLiteral(callee_pred)) callee_tpred = 
            modTranslate(callee_pred,false,eod,args); 
          if (callee_tpred != null) {
            ev.addElement(GC.not(callee_tpred));
          }
          if (ex instanceof EverythingExpr) {
            caller_iterator.reset();
            while (caller_iterator.hasNext()) {
              Object exx = caller_iterator.next();
              Expr caller_pred = caller_iterator.cond();
              if (exx instanceof EverythingExpr) {
                if (addImplication(ev,callee_tpred,caller_pred)) continue OUTER;
              }
            }
            modChecksComplete(mge.precondition,callee_tprecondition,ev,loccall,calleeLoc,callerLoc,true);
          } else if (ex instanceof NothingExpr) {
            // skip
          } else if (ex instanceof FieldAccess) {
            FieldAccess fa = (FieldAccess)ex;
            Expr eeod = (fa.od instanceof ExprObjectDesignator) ? 
                ((ExprObjectDesignator)fa.od).expr : null;
            Expr lval = eeod == null ? null 
                : modTranslate(eeod, false,  eod, args);
            
            modifiesCheckFieldHelper(lval,loccall, fa.decl, calleeLoc, 
                callee_tpred, callee_tprecondition,true);
            // A bit of a hack - the FieldHelper routine iterates over
            // all of the caller frame conditions, so we short-circuit
            // that here
            kk = mg.size();
          } else if (ex instanceof ArrayRefExpr) {
            Expr array= modTranslate(((ArrayRefExpr)ex).array, false,  eod, args );
            Expr index= modTranslate(((ArrayRefExpr)ex).index, false,  eod, args );
            modifiesCheckArray(array,index,loccall,calleeLoc,callee_tpred, callee_tprecondition);
            // A bit of a hack - the helper routine iterates over
            // all of the caller frame conditions, so we short-circuit
            // that here
            kk = mg.size();
          } else if (ex instanceof WildRefExpr) {
            ObjectDesignator odd = ((WildRefExpr)ex).od;
            Expr e1 = null;
            if (odd instanceof ExprObjectDesignator) {
              e1 = modTranslate(((ExprObjectDesignator)odd).expr,
                  false,eod,args);
              addAllocExpression(ev,e1);
            }
            //System.out.println("CALLEE " + ex);
            caller_iterator.reset();
            while (caller_iterator.hasNext()) {
              Object exx = caller_iterator.next();
              //System.out.println("CALLER " + exx);
              Expr caller_pred = caller_iterator.cond();
              if (exx instanceof EverythingExpr) {
                if (addImplication(ev,callee_tpred,caller_pred)) continue OUTER;
              } else if (exx instanceof WildRefExpr) {
                ObjectDesignator oddd = ((WildRefExpr)exx).od;
                if ((odd instanceof TypeObjectDesignator) && (oddd instanceof TypeObjectDesignator)) {
                  Type t = ((TypeObjectDesignator)odd).type;
                  Type tt = ((TypeObjectDesignator)oddd).type;
                  if (t == tt || ((t instanceof TypeSig) && Types.isSubclassOf(tt,(TypeSig)t)) ) {
                    if (addImplication(ev,callee_tpred,caller_pred)) continue OUTER;
                  }
                } else if (odd instanceof ExprObjectDesignator && oddd instanceof ExprObjectDesignator) {
                  Expr e2 = modTranslate(((ExprObjectDesignator)oddd).expr,
                      true,null);
                  e1 = GC.nary(TagConstants.REFEQ,e1,e2);
                  addImplication(ev,e1,callee_tpred,caller_pred);
                } else {
                  //System.out.println("COMPARE TO " + odd.getClass() + " " + oddd.getClass());
                }
              }
            }
            //System.out.println("MCC A: " + mge.precondition);
            //System.out.println("MCC B: " + callee_tprecondition);
            //System.out.println("MCC C: " + ev);
            modChecksComplete(mge.precondition,callee_tprecondition,ev,loccall,calleeLoc,callerLoc,true);
          } else if (ex instanceof ArrayRangeRefExpr) {
            ArrayRangeRefExpr aexpr = (ArrayRangeRefExpr)ex;
            Expr array = aexpr.array;
            Expr lowIndex = aexpr.lowIndex;
            Expr highIndex = aexpr.highIndex;
            Expr ao = modTranslate(array,false,eod,args);
            Expr al = lowIndex == null ? null :
              modTranslate(lowIndex,false,eod,args); 
            Expr ah = highIndex == null ? null :
              modTranslate(highIndex,false,eod,args); 
            addAllocExpression(ev,ao);
            caller_iterator.reset();
            while (caller_iterator.hasNext()) {
              Object exx = caller_iterator.next();
              Expr caller_pred = caller_iterator.cond();
              if (exx instanceof EverythingExpr) {
                if (addImplication(ev,callee_tpred,caller_pred)) continue OUTER;
              } else if (exx instanceof ArrayRangeRefExpr) {
                ArrayRangeRefExpr aaexpr = (ArrayRangeRefExpr)exx;
                Expr aarray = aaexpr.array;
                Expr alowIndex = aaexpr.lowIndex;
                Expr ahighIndex = aaexpr.highIndex;
                Expr aao = modTranslate(aarray,true,null);
                Expr aal = alowIndex == null ? null :
                  modTranslate(alowIndex,true,null); 
                Expr aah = ahighIndex == null ? null :
                  modTranslate(ahighIndex,true,null); 
                if (ah == null && aah != null) continue; // FIXME - could compare against the length of ao
                aao = GC.nary(TagConstants.REFEQ,ao,aao);
                aal = aal == null ? null :
                  GC.nary(TagConstants.INTEGRALLE,aal,
                      al != null ? al: GC.zerolit);
                aah = aah == null ? null :
                  GC.nary(TagConstants.INTEGRALLE,ah,aah);
                aal = aal == null ? aah : aah == null ? aal : GC.and(aal,aah);
                aao = aal == null ? aao : GC.and(aao,aal);
                addImplication(ev,aao,callee_tpred,caller_pred);
              } else if (exx instanceof ArrayRefExpr) {
                if (ah == null) continue; // FIXME - could compare against the length of ao
                ArrayRefExpr aaexpr = (ArrayRefExpr)exx;
                Expr aarray = aaexpr.array;
                Expr aindex = aaexpr.index;
                Expr aao = modTranslate(aarray,true,null);
                aindex = modTranslate(aindex,true,null); 
                aao = GC.nary(TagConstants.REFEQ,ao,aao);
                Expr aal = GC.nary(TagConstants.INTEGRALLE,aindex,
                    al != null ? al: GC.zerolit);
                Expr aah = GC.nary(TagConstants.INTEGRALLE,ah,aindex);
                aal = GC.and(aal,aah);
                aao = GC.and(aao,aal);
                addImplication(ev,aao,callee_tpred,caller_pred);
              }
            }
            modChecksComplete(mge.precondition,callee_tprecondition,ev,loccall,calleeLoc,callerLoc,true);
          } else {
            System.out.println("Modifies Check not implemented for " + ex.getClass());
            caller_iterator.reset();
            while (caller_iterator.hasNext()) {
              Object exx = caller_iterator.next();
              Expr caller_pred = caller_iterator.cond();
              if (exx instanceof EverythingExpr) {
                if (addImplication(ev,callee_tpred,caller_pred)) continue OUTER;
              }
            }
            modChecksComplete(mge.precondition,callee_tprecondition,ev,loccall,calleeLoc,callerLoc,true);
          }
        }
      }
    } finally {
      pFreshResult = false;
    }
  }
  
  
  private boolean isTrueLiteral(Expr p) {
    if (p == null) return true;
    if (!(p instanceof LiteralExpr)) return false;
    LiteralExpr lit = (LiteralExpr)p;
    if (lit.getTag() != TagConstants.BOOLEANLIT) return false;
    Object value = lit.value;
    return ((Boolean)value).booleanValue() ;
  }
  
  private boolean addImplication(ExprVec ev, Expr callee_tpred, Expr caller_pred) {
    Expr caller_tpred = null;
    if (!isTrueLiteral(caller_pred)) caller_tpred = 
      modTranslate(caller_pred,false,null);  
    return addTImplication(ev,callee_tpred,caller_tpred);
  }
  private boolean addTImplication(ExprVec ev, Expr callee_tpred, Expr caller_tpred) {
    if (callee_tpred != null && caller_tpred != null) {
      ev.addElement(GC.implies(callee_tpred,caller_tpred));
    } else if (callee_tpred != null && caller_tpred == null) {
      return true;
    } else if (callee_tpred == null && caller_tpred != null) {
      ev.addElement(caller_tpred);
    } else {
      return true; // obviously ok - both  are unconditional
    }
    return false;
  }
  
  
  private void addImplication(ExprVec ev, Expr e, Expr callee_tpred, Expr caller_pred) {
    Expr caller_tpred = null;
    if (!isTrueLiteral(caller_pred)) caller_tpred = 
      modTranslate(caller_pred,true,null);  
    addTImplication(ev,e,callee_tpred,caller_tpred);
  }
  private void addTImplication(ExprVec ev, Expr e, Expr callee_tpred, Expr caller_tpred) {
    if (callee_tpred != null && caller_tpred != null) {
      ev.addElement(GC.and(e,GC.implies(callee_tpred,caller_tpred)));
    } else if (callee_tpred != null && caller_tpred == null) {
      ev.addElement(e);
    } else if (callee_tpred == null && caller_tpred != null) {
      ev.addElement(GC.and(e,caller_tpred));
    } else {
      ev.addElement(e);
    }
  }
  
  
  void modifiesCheckArray(Expr array, Expr arrayIndex, int callLoc) {
    kindOfModCheck = "assignment";
    modifiesCheckArray(array,arrayIndex,callLoc,Location.NULL,null,null);
  }
  
  /** Adds an expression into ev stating that e is allocated now but was
   * not allocated in the pre-state.  No expression is added to ev if it
   * is definitely false that e is fresh - such as if e is this or is null
   * (meaning the field is static).  Otherwise if pFreshResult is true,
   * a literal True expression is added.  Otherwise some non-trivial 
   * expression is added.
   * <p>
   * Also uses pFreshResult, which must be true iff e is known to be fresh
   * since the prestate.
   * @param ev A vector to accumulate assertions
   * @param e  An expression to be tested for freshness
   */
  private void addAllocExpression(ExprVec ev, Expr e) {
    if (e == null) return;
    if (e instanceof ThisExpr) return;
    if ((e instanceof VariableAccess) && 
        (((VariableAccess)e).id == thisId)) return;
    if (pFreshResult) {
      ev.addElement(GC.truelit);
      return;
    }
    ev.addElement (
        GC.and(
            GC.nary(TagConstants.ISALLOCATED,e,
                TrAnExpr.trSpecExpr(GC.allocvar)),
                GC.not(GC.nary(TagConstants.ISALLOCATED,e,
                    TrAnExpr.trSpecExpr(GC.allocvar,premap,premap)))
        )
    );
  }
  
  void modifiesCheckArray(Expr array, Expr arrayIndex, int callLoc, int calleeLoc,
      Expr callee_tpred, Expr callee_tprecondition) {
    // FIXME - I don't think this handles this and super that are not the
    // prefix.
    if (!issueCautions) return;
    // We need to create a translated predicate expression that is true
    // if the lhs is allowed to be modified and false if it is not
    // allowed to be modified.  This will be an OR across each of the
    // modify pragmas.  Each pragma will contribute
    //   - obviously false if it is not the same declaration or same type
    //   - obviously true if is is the same declaration and both have 'this'
    //  as the od and the condition is true
    //   - obviously true (and then no check) if it is modifies everything
    //  with a true condition
    //   - some expression which is the AND of the condition and that
    //  the lhs matches the modifies expression:
    //      fields must have the same object designator
    //      arrays must have the same array expression and same index
    ModifiesGroupPragmaVec mg = GetSpec.getCombinedMethodDecl(rdCurrent).modifies;
    for (int kk=0; kk<mg.size(); ++kk) {
      ModifiesGroupPragma mge = mg.elementAt(kk);
      int callerLoc = mge.clauseLoc;
      ExprVec ev = ExprVec.make(10);
      addAllocExpression(ev,array); 
      if (callee_tpred != null) ev.addElement(GC.not(callee_tpred));
      ModifiesIterator caller_iterator = new ModifiesIterator(mge.items,true);
      THISGROUP: while (caller_iterator.hasNext()) {
        Object ex = caller_iterator.next();
        Expr caller_pred = caller_iterator.cond();
        Expr caller_tpred = null;
        if (!isTrueLiteral(caller_pred)) caller_tpred = 
          modTranslate(caller_pred,true,null);
        if (ex instanceof FieldAccess) {
        } else if (ex instanceof FieldDecl) {
        } else if (ex instanceof ArrayRefExpr) {
          if (array != null) {
            //System.out.println("MATCHING AGAINST ARRAY " );
            Expr ao = ((ArrayRefExpr)ex).array;
            Expr ai = ((ArrayRefExpr)ex).index;
            ao = modTranslate(ao,true,null);
            ai = modTranslate(ai,true,null); 
            ao = GC.nary(TagConstants.REFEQ,array,ao);
            ai = GC.nary(TagConstants.INTEGRALEQ,arrayIndex,ai);
            ao = GC.and(ao,ai);
            addTImplication(ev,ao,callee_tpred,caller_tpred);
          }
        } else if (ex instanceof NothingExpr) {
          //System.out.println("MATCHING AGAINST NOTHING " );
        } else if (ex instanceof EverythingExpr) {
          //System.out.println("MATCHING AGAINST EVERYTHING " );
          if (addTImplication(ev,callee_tpred,caller_tpred)) { ev = null; break THISGROUP; }
          
        } else if (ex instanceof ArrayRangeRefExpr) {
          if (array != null) {
            //System.out.println("MATCHING AGAINST ARRAY RANGE " );
            ArrayRangeRefExpr a = (ArrayRangeRefExpr)ex;
            Expr ao = modTranslate(a.array,true,null);
            Expr al = a.lowIndex == null ? null :
              modTranslate(a.lowIndex,true,null); 
            Expr ah = a.highIndex == null ? null :
              modTranslate(a.highIndex,true,null); 
            ao = GC.nary(TagConstants.REFEQ,array,ao);
            al = al == null ? null :
              GC.nary(TagConstants.INTEGRALLE,al,arrayIndex);
            ah = ah == null ? null :
              GC.nary(TagConstants.INTEGRALLE,arrayIndex,ah);
            al = al == null ? ah : ah == null ? al :
              GC.and(al,ah);
            ao = al == null ? ao : GC.and(ao,al);
            addTImplication(ev,ao,callee_tpred,caller_tpred);
          }
        } else if (ex instanceof WildRefExpr) {
          // FIX ME DAVID!
        } else {
          System.out.println("COMPARE TO " + ex.getClass());
        }
      }
      if (ev != null) modChecksComplete(mge.precondition,
          callee_tprecondition,ev,callLoc,
          calleeLoc==Location.NULL ? callerLoc : calleeLoc,
              calleeLoc==Location.NULL ? Location.NULL: callerLoc, true);
    }
  }
  
  /* UNUSED
   private boolean modChecksComplete(Expr precondition, ExprVec ev, int callLoc, int aloc, boolean doCheck) {
   return modChecksComplete(precondition,null,ev,callLoc,aloc,Location.NULL,doCheck);
   }
   */
  
  // Returns true if definitely not modified
  // Returns false if possibly or definitely modified
  private boolean modChecksComplete(Expr precondition, Expr tprecond2, 
      ExprVec ev, int callLoc, int aloc, int aloc2, boolean doCheck) {
    if (!doCheck) {
      //TrAnExpr.closeForClause();
      if (ev.size() == 0) return true;
      return false;
    }
    if (NoWarn.getChkStatus(TagConstants.CHKMODIFIES,callLoc,aloc==Location.NULL?callLoc:aloc)
        != TagConstants.CHK_AS_ASSERT) {
      TrAnExpr.closeForClause();
      return false;
    }
    if (aloc2 != Location.NULL) {
      if (NoWarn.getChkStatus(TagConstants.CHKMODIFIES,callLoc,aloc2)
          != TagConstants.CHK_AS_ASSERT) {
        TrAnExpr.closeForClause();
        return false;
      }}
    Expr tprecondition = modTranslate(precondition,true,null);
    if (tprecond2 != null) {
      tprecondition = GC.and(tprecondition, tprecond2);
    }
    if (ev.size() == 0 && isTrueLiteral(precondition)) {
      if (aloc == TagConstants.NULL) ErrorSet.error(callLoc, 
          "There is no assignable clause allowing this " +
          kindOfModCheck);
      else ErrorSet.error(callLoc, 
          "There is no assignable clause allowing this "
          + kindOfModCheck,aloc);
      if (aloc2 != Location.NULL) ErrorSet.assocLoc(aloc2);
    } else if (aloc == Location.NULL) {
      //System.out.println("Generating a modifies check " + ev.size());    
      translator.addNewAssumptionsNow();
      translator.addCheck(callLoc,TagConstants.CHKMODIFIES, 
          GC.implies(tprecondition,GC.or(ev)));
    } else {
      //System.out.println("Generating a modifies check " + ev.size());    
      translator.addNewAssumptionsNow();
      translator.addCheck(callLoc,TagConstants.CHKMODIFIES, 
          GC.implies(tprecondition,GC.or(ev)),aloc,aloc2);
      // FIXME - could also include a list of locations from the caller modifies group
      // FIXME will aloc2 be sensitive to warnings that are shut off?
    }
    TrAnExpr.closeForClause();
    return false;
  }
  
  /** This class enables iterating over the set of store-ref
   * locations in a ModifiesGroupPragma.  It also has the ability
   * to include in the iteration the contents of datagroups that
   * are part of the set of store-ref locations.
   * 
   * @author David Cok
   *
   */
  static class ModifiesIterator {
    
    /** The set of store-ref locations over which to iterate. */
    final private CondExprModifierPragmaVec mp;
    
    /** Fields that have yet to be iterated over.  This
     * is a list of FieldAccess objects. */
    final private List others = new LinkedList();
    
    /** The datagroups that have already been expanded */
    final private List done = new LinkedList();
    
    /** If true, then datagroups are expanded and their contents
     * made part of the iteration.
     */
    final private boolean expandDatagroups;
    
    /** If true, then field wild card store refs (obj.* and
     * Type.*) are expanded and their contents made part of the
     * iteration.
     */
    final private boolean expandWild;
    
    /** An array index into mp */
    private int i = 0;
    
    /** Creates an iterator over the store-ref locations in
     * the CondExprModifierPragmaVec.  The expandWild parameter
     * is set false.
     * @param mp The set of store-ref locations over which to
     *      iterate
     * @param expandDatagroups if true, then datagroups are 
     *      expanded and their contents (recursively) become
     *      steps in the iteration
     */
    public ModifiesIterator(CondExprModifierPragmaVec mp, boolean expandDatagroups) {
      this(mp,expandDatagroups,false);
    }
    
    /** Creates an iterator over the store-ref locations in
     * the CondExprModifierPragmaVec.
     * @param mp The set of store-ref locations over which to
     *      iterate
     * @param expandDatagroups if true, then datagroups are 
     *      expanded and their contents (recursively) become
     *      steps in the iteration
     * @param expandWild if true, then store-ref expressions
     *      of the form  obj.* are expanded into their
     *      individual fields
     */
    public ModifiesIterator(CondExprModifierPragmaVec mp, 
        boolean expandDatagroups, boolean expandWild) {
      this.mp = mp;
      this.expandDatagroups = expandDatagroups;
      this.expandWild = expandWild;
      i = 0;
    }
    
    /** Resets the iteration back to the beginning */
    public void reset() {
      i = 0;
      others.clear();
      done.clear();
    }
    
    /** Returns true if there is more to the iteration */
    public boolean hasNext() {
      return i < mp.size() || !others.isEmpty();
    }
    
    /** Returns the next element of the iteration; only valid
     * if hasNext returns true, otherwise throws an exception
     * @return the next element of the iteration
     * @throws NoSuchElementException if there are no more elements
     *      in the iteration
     */
    public Object next() throws NoSuchElementException {
      Object ex;
      if (!others.isEmpty()) {
        ex = others.remove(0);
      } else if (i >= mp.size()) {
        throw new NoSuchElementException();
      } else {
        condExpr = mp.elementAt(i).cond;
        ex = mp.elementAt(i).expr;
        ++i;
        done.clear();
      }
      if (ex instanceof FieldAccess) {
        if (expandDatagroups) add(((FieldAccess)ex).od,((FieldAccess)ex).decl);
      } else if (expandWild && (ex instanceof WildRefExpr)) {
        //System.out.println("EXPANDING " + Location.toString(((WildRefExpr)ex).getStartLoc()));
        ObjectDesignator od = ((WildRefExpr)ex).od;
        addFields(od);
      }
      
      return ex;
    }
    
    Expr condExpr = null;
    public Expr cond() {
      return condExpr;
    }
    
    
    int limit = Main.options().mapsUnrollCount;
    
    /** Adds all the fields of the od (whether it is a type
     * or an object) into the 'others' list as FieldAccess
     * items.
     * @param od
     */
    private void addFields(ObjectDesignator od) {
      Type type;
      boolean stat;
      if (od instanceof TypeObjectDesignator) {
        type = ((TypeObjectDesignator)od).type;
        stat = true;
      } else if (od instanceof ExprObjectDesignator) {
        type = TypeCheck.inst.getType(((ExprObjectDesignator)od).expr);
        stat = false;
      } else {
        // FIXME ???
        return;
      }
      if (type instanceof javafe.tc.TypeSig) {
        TypeSig ts = (TypeSig)type;
        EnvForTypeSig env;
        if (stat)
          env = (EnvForTypeSig)FlowInsensitiveChecks.staticenvDecoration.get(ts.getTypeDecl());
        else
          env = (EnvForTypeSig)FlowInsensitiveChecks.envDecoration.get(ts.getTypeDecl());
        if (env == null) env = ((TypeSig)type).getEnv(stat);
        // The true in the following means all fields are gotten,
        // whether or not they are visible or inherited.
        // It does also return ghost and model fields.
        javafe.ast.FieldDeclVec fds = env.getFields(true);
        for (int i=0; i<fds.size(); ++i) {
          FieldDecl fd = fds.elementAt(i);
          if (stat != Modifiers.isStatic(fd.modifiers)) continue;
          FieldAccess fa = FieldAccess.make(od,fd.id,Location.NULL);
          fa.decl = fd;
          fa = (FieldAccess)javafe.tc.FlowInsensitiveChecks.setType(fa,fd.type);
          others.add(fa);
          //System.out.println("ADDING " + fd.id + " " + fd.type);
        }
      } // FIXME - what other types are there to consider?
    }
    
    private void add(ObjectDesignator od, FieldDecl d) {
      if (count(d) >= limit) return;
      done.add(d);
      if (od == null || !(od instanceof ExprObjectDesignator)) {
        others.addAll(Datagroups.get(d));
      } else {
        Expr e = ((ExprObjectDesignator)od).expr;
        Iterator i = Datagroups.get(d).iterator();
        Hashtable h = new Hashtable();
        h.put(Substitute.thisexpr,e);
        while (i.hasNext()) {
          Object o = i.next();
          if (o instanceof FieldDecl) {
            System.out.println("FD " + o);
          } else if (o instanceof Expr) {
            Expr ee = (Expr)o;
            //System.out.println("EXPR " + ee.getClass() + " " + ee);
            ee = Substitute.doSubst(h,ee);
            others.add(ee);
          } else {
            System.out.println("OTYPE " + o.getClass());
          }
        }
      }
    }
    
    private int count(FieldDecl d) {
      int k = 0;
      Iterator i = done.iterator();
      while (i.hasNext()) {
        if (i.next() == d) ++k;
      }
      return k;
    }
    
  }
  
  private Expr modTranslate(Expr e, boolean old, Expr thisexpr) {
    return modTranslate(e,old,thisexpr,null);
  }
  private Expr modTranslate(Expr e, boolean old, Expr thisexpr, Hashtable args) {
    TrAnExpr.initForClause(true);
    if (old) return TrAnExpr.trSpecExpr(e,premap,premap,thisexpr);
    else if (args == null)  return TrAnExpr.trSpecExpr(e,thisexpr);
    else     return TrAnExpr.trSpecExpr(e,args,args,thisexpr);
  }
  
}
