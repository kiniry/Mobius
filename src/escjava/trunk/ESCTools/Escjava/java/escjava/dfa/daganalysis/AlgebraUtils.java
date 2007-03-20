package escjava.dfa.daganalysis;

/*
 * Created on Mar 16, 2006
 */

import java.util.Hashtable;

import org.apache.tools.ant.taskdefs.condition.IsSet;

import javafe.ast.*;
import javafe.util.Assert;

import escjava.ast.*;
import escjava.prover.Atom;
import escjava.sp.VarMap;
import escjava.translate.*;

import escjava.ast.TagConstants;

/**
 * @author Mikolas
 * 
 * This class encapsulates algebra-like operations on expressions.
 */
public class AlgebraUtils {

    /**
     * Computes the set difference for the given var declaration vectors.
     * 
     * @param a
     *            from this vector we subtract
     * @param b
     *            this vector will be subtracted
     * @result a new vector that will contain the difference (alway non-null),
     *         i.e., it will contain those elements from <code>a</code> that
     *         are not in <code>b</code>
     */
    public static GenericVarDeclVec difference(
            /* @ non_null @ */GenericVarDeclVec a, /* @ non_null @ */
            GenericVarDeclVec b) {
        GenericVarDeclVec retv = GenericVarDeclVec.make();
        for (int i = 0; i < a.size(); i++) {
            GenericVarDecl vd = a.elementAt(i);

            if (!b.contains(vd)) {
                // add the vd in the result only if it's not in b
                retv.addElement(vd);
            }
        }
        return retv;
    }

    public static boolean contains(/*@ non_null @*/ExprVec ev, /*@ non_null @*/Expr e) {
        for (int i = 0; i < ev.size(); i++) {
            if (isSame(ev.elementAt(i), e))
                return true;
        }
        return false;
    }
    
    public static ExprVec difference(
            /*@ non_null @*/ExprVec a, 
            /*@ non_null @*/ExprVec b) {
        ExprVec diff = ExprVec.make();
        for (int i = 0; i < a.size(); i++) {            
            Expr e = a.elementAt(i);

            if (!contains(b, e)) {
                // add the e in the result only if it's not in b
                diff.addElement(e);
            }
        }
        return diff;
    }

    
    public static boolean subset(GenericVarDeclVec vec1, GenericVarDeclVec vec2) {
        for (int i = 0; i < vec1.size(); i++) {
            GenericVarDecl vd1 = vec1.elementAt(i);

            if (!vec2.contains(vd1)) {
                return false;
            }
        }
        return true;
    }

    public static boolean setEquals(GenericVarDeclVec vec1,
            GenericVarDeclVec vec2) {
        return subset(vec1, vec2) && subset(vec2, vec1);
    }

    public static boolean intersect(GenericVarDeclVec vec1,
            GenericVarDeclVec vec2) {
        for (int i = 0; i < vec1.size(); i++) {
            GenericVarDecl decl1 = vec1.elementAt(i);
            if (vec2.contains(decl1))
                return true;
        }
        return false;
    }

    static void andAdd(ExprVec ev, Expr e) {
        if (e.getTag() == TagConstants.BOOLAND) {
            NaryExpr nex = (NaryExpr) e;
            ExprVec toAdd = nex.exprs;
            setAppend(ev, toAdd);
        } else {
            setAdd(e, ev);
        }

    }

    static void orAdd(ExprVec ev, Expr e) {
        if (e.getTag() == TagConstants.BOOLOR) {
            NaryExpr nex = (NaryExpr) e;
            ExprVec toAdd = nex.exprs;
            setAppend(ev, toAdd);
        } else {
            setAdd(e, ev);
        }
    }

    static ExprVec isEQ(Expr e) {
        if (e.getTag() == TagConstants.ANYEQ) {
            ExprVec terms = ((NaryExpr) e).exprs;
            Assert.notFalse(terms.size() == 2,
                    "I guess I don't understand this op.");
            
            return terms;
        }
        
        return null;
    }
    
    //@ ensures \result != null;
    //@ ensures \result.size() == target.size();
    static ExprVec subst(/*@ non_null @*/GenericVarDecl vd, /*@ non_null @*/Expr val, /*@ non_null @*/ExprVec target) {
        ExprVec retv = ExprVec.make(target.size());
        for (int i = 0; i < target.size(); i++) {
            Expr te = target.elementAt(i);
            te = GC.subst(vd, val, te);
            retv.addElement(te);
        }
        
        return retv;
    }
    
    public static Expr removeLetExpressions(Expr e) {
         if (e instanceof NaryExpr) {
            NaryExpr ne = (NaryExpr) e;
            ExprVec es = ne.exprs;
            
            ExprVec newVec = ExprVec.make(es.size());
            for (int i = 0; i < es.size(); i++) {
                newVec.addElement(removeLetExpressions(es.elementAt(i)));
            }
            
            NaryExpr retv = NaryExpr.make(ne.sloc, ne.eloc, ne.op, ne.methodName, newVec);
            return retv;
        }
        
         
        if (e instanceof QuantifiedExpr) {            
            QuantifiedExpr qe = (QuantifiedExpr) e;
            Expr inside = qe.expr;
            inside = removeLetExpressions(inside);
            e = QuantifiedExpr.make(qe.sloc, qe.eloc, qe.quantifier, qe.vars, qe.rangeExpr, inside, qe.nopats, qe.pats);                    
        }
         
                
        if (e instanceof QuantifiedExpr) {            
            QuantifiedExpr qe = (QuantifiedExpr) e;
            
            if (qe.quantifier != TagConstants.FORALL)
                return e;
        
            
            
            Expr inside = qe.expr;
            inside = removeLetExpressions(inside);
            if (inside.getTag() == TagConstants.BOOLIMPLIES) {
                NaryExpr impl = (NaryExpr) inside;
                
                ExprVec exprs = impl.exprs;
                Expr left = exprs.elementAt(0);
                Expr right = exprs.elementAt(1);
                ExprVec les = flattenAnd(left);
                for (int i = 0; i < les.size();) {
                    Expr le = les.elementAt(i);
  
                    ExprVec eqsides = isEQ(le);
                    if (isEQ(le) != null) {
                        GenericVarDecl leftE = null;
                        Expr rightE = null;
                        GenericVarDecl v1 = eqsides.elementAt(1) instanceof VariableAccess ? ((VariableAccess) eqsides.elementAt(1)).decl : null;
                        GenericVarDecl v0 = eqsides.elementAt(0) instanceof VariableAccess ? ((VariableAccess) eqsides.elementAt(0)).decl : null;
                        
                        
                        // look for a side of the equality that is a variable quantified over in this expression
                        if (v1 != null &&   qe.vars.contains(v1)) {
                            leftE = v1;
                            rightE = eqsides.elementAt(0);
                        } else
                            if (v0 != null && qe.vars.contains(v0)) {
                                leftE = v0;
                                rightE = eqsides.elementAt(1);
                            }
                            
                        if (leftE != null) {
                            if (!usesVar(leftE, rightE)) {
                                // check if leftE is not continained in rightE
                                
                                // at least one side of the equality is
                                // quantified over,
                                // remove it from the expression

                                // remove the element the equality from the left
                                // part of the implication
                                les.removeElementAt(i);

                                // apply substituion on the left part of the
                                // implication
                                les = subst(leftE, rightE, les);

                                // apply substituion on the right part of the
                                // implication
                                right = GC.subst(leftE, rightE, right);

                                continue;
                            }
                        }
                        
                    }
                    
                    i++; // this is skipped when an element is removed from
                            // [les], due to the [continue]
                }
                
                
                Expr retv;
                
                
                if (les.size() == 0) {
                    // all the elemnts on the lefthand side were removed
                    retv =  right;
                } else {
                    // recreate the implication
                    retv =  GC.implies(andSimple(les), right);
                }
                QuantifiedExpr newQE = QuantifiedExpr.make(qe.sloc, qe.eloc, qe.quantifier, qe.vars, qe.rangeExpr, retv, qe.nopats, qe.pats);
                retv = pruneQuantifiedExpr(newQE);
                
                return retv;
                
            }
            
            
        }
        
        return e;
        
    }
    
    
    /**
     * And two expressions in such a way that the n-ary and is exploited.
     * 
     * @param e1
     *            an <code>Expr</code> value
     * @param e2
     *            an <code>Expr</code> value
     * @return expression representing the and value of the given parameters
     */
    public static Expr and(Expr e1, Expr e2) {
        ExprVec retvExprs = ExprVec.make();
        andAdd(retvExprs, e1);
        andAdd(retvExprs, e2);
        Expr retv = GC.and(retvExprs);
        return retv;
    }
    
    public static Expr andSimple(ExprVec ev) {
        if (ev.size() == 0) {
            return GC.truelit;
        } else {
            if (ev.size() == 1)
                return ev.elementAt(0);
            else {
                return GC.and(ev);
            }
        }
    }

    public static QuantifiedExpr recreateQuantifiedExpr(QuantifiedExpr qexpr,
            Expr newBoundExpr) {
        return QuantifiedExpr.make(qexpr.sloc, qexpr.eloc, qexpr.quantifier,
                qexpr.vars, qexpr.rangeExpr, newBoundExpr, qexpr.nopats,
                qexpr.pats);
    }

    public static NaryExpr recreateNary(NaryExpr old, ExprVec newChildren) {
        NaryExpr retv = NaryExpr.make(old.sloc, old.eloc, old.op,
                old.methodName, newChildren);
        return retv;
    }

    public static Expr recreateCommutativeAssociativeNary(NaryExpr old,
            ExprVec newChildren) {
        if (newChildren.size() == 1) {
            return newChildren.elementAt(0);
        } else {
            return recreateNary(old, newChildren);
        }
    }

    // @ require old.getTag == TaTagConstants.BOOLAND;
    public static Expr recreateAnd(NaryExpr old, ExprVec newChildren) {
        if (containsBooleanLiteral(newChildren, false)) {
            return GC.falselit;
        } else {
            if (containsComplementary(newChildren)) {
                return GC.falselit;
            } else {
                return recreateCommutativeAssociativeNary(old, newChildren);
            }
        }
    }

    // @ require assert old.getTag() == TagConstants.BOOLOR;
    public static Expr recreateOr(NaryExpr old, ExprVec newChildren) {
        if (containsBooleanLiteral(newChildren, true)) {
            return GC.truelit;
        } else {
            if (containsComplementary(newChildren)) {
                return GC.truelit;
            } else {
                return recreateCommutativeAssociativeNary(old, newChildren);
            }
        }
    }

    public static Expr consolidateAnds(Expr expr) {
        Expr retv;
        expr = stripOffLabels(expr);

        if (expr instanceof NaryExpr) {
            NaryExpr nex = (NaryExpr) expr;
            ExprVec exprs = nex.exprs;

            switch (expr.getTag()) {
            case TagConstants.BOOLAND: {
                // remove and cascading if possible
                ExprVec retvExprs = ExprVec.make();
                for (int i = 0; i < exprs.size(); i++) {
                    Expr e = exprs.elementAt(i);
                    Expr retvE = consolidateAnds(e);
                    andAdd(retvExprs, retvE);
                }

                retv = recreateAnd(nex, retvExprs);
            }
                break;
            case TagConstants.BOOLOR: {
                ExprVec retvExprs = ExprVec.make();
                // remove or cascading if possible
                for (int i = 0; i < exprs.size(); i++) {
                    Expr e = exprs.elementAt(i);
                    Expr retvE = consolidateAnds(e);
                    orAdd(retvExprs, retvE);
                }
                retv = recreateOr(nex, retvExprs);
            }
                break;
            case TagConstants.IMPLIES:
            case TagConstants.EXPLIES:
            case TagConstants.IFF: {
                // treat implications
                Expr left = exprs.elementAt(0);
                Expr right = exprs.elementAt(1);
                if (isSame(left, right)) {
                    retv = GC.truelit; // replace with TRUE
                } else {
                    retv = expr; // leave unchanged
                }
            }
                break;
            default: {
                // for any other type of expression recursively plunge into one
                // more level deeper
                ExprVec retvExprs = ExprVec.make();
                for (int i = 0; i < exprs.size(); i++) {
                    Expr e = exprs.elementAt(i);
                    Expr retvE = consolidateAnds(e);
                    retvExprs.addElement(retvE);
                }
                retv = NaryExpr.make(nex.sloc, nex.eloc, nex.op,
                        nex.methodName, retvExprs); // recreate from simplified
                                                    // children
            }
                break;
            }
        } else {
            if (expr instanceof QuantifiedExpr) {
                QuantifiedExpr q = (QuantifiedExpr) expr;
                Expr boundExpr = q.expr;
                Expr newBoundExpr = consolidateAnds(boundExpr);
                retv = recreateQuantifiedExpr(q, newBoundExpr);
            } else {
                retv = expr; // not an nary expression, skipping
            }
        }

        return retv;
    }

    public static boolean isComplementary(Expr e1, Expr e2) {
        if (e1.getTag() == TagConstants.BOOLNOT) {
            NaryExpr nex = (NaryExpr) e1;
            e1 = nex.exprs.elementAt(0);
            e2 = e2;
        } else {
            if (e2.getTag() == TagConstants.BOOLNOT) {
                NaryExpr nex = (NaryExpr) e2;
                e2 = nex.exprs.elementAt(0);
                e1 = e1;
            } else {
                return false;
            }
        }

        return isSame(e1, e2);

    }

    public static boolean containsComplementary(ExprVec evec) {
        for (int i = 0; i < evec.size() - 1; i++) {
            for (int j = i + 1; j < evec.size(); j++) {
                Expr e1 = evec.elementAt(i);
                Expr e2 = evec.elementAt(j);
                if (isComplementary(e1, e2)) {
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean containsBooleanLiteral(ExprVec evec, boolean value) {
        for (int i = 0; i < evec.size(); i++) {
            Expr e = evec.elementAt(i);
            if (isBooleanLiteral(e, value)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Strips off labels from the given expression.
     * 
     * @param pred
     *            the expression from which the labels will be stripped off
     * @result expression equivalent to the given one without the outter labels
     */
    public static Expr stripOffLabels(Expr pred) {
        Expr retv = pred;
        while (retv.getTag() == TagConstants.LABELEXPR) {
            LabelExpr le = (LabelExpr) retv;
            retv = (le.expr);
        }

        return retv;
    }

    //@ requires expr.getTag() == TagConstants.BOOLAND || expr.getTag() ==  TagConstants.BOOLOR;
    //@ requires expr.exprs.size() > 0;
    public static Expr pruneAndOrNary(NaryExpr expr) {
            ExprVec uniqueLits = removeDuplicates(expr.exprs);

            Expr retv;
            if (uniqueLits.size() > 1) {
                retv = NaryExpr.make(expr.sloc, expr.eloc, expr.op, expr.methodName, uniqueLits);
            } else {
                // assert uniqueLits.size() == 1;
                retv = uniqueLits.elementAt(0);
            }

            return retv;
        }

    
    /**
     * Test whether a given expression is a boolean literal with a specified
     * value.
     * 
     * @param expr
     *            tested expression
     * @param value
     *            a <code>boolean</code> value representing the desired value
     *            of the expression
     * @return a <code>boolean</code> value indicating that the given
     *         expression is a boolean literal with the given value
     */
    public static boolean isBooleanLiteral(Expr expr, boolean value) {
        Expr stripped = stripOffLabels(expr);
        if (expr instanceof LiteralExpr) {
            LiteralExpr le = (LiteralExpr) expr;
            Object storedValue = le.value;
            if (storedValue instanceof Boolean) {
                Boolean storedBoolean = (Boolean) storedValue;
                return storedBoolean.booleanValue() == value;
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    /**
     * Determines whether a given expression is the true literal.
     * 
     * @param expr
     *            the inspected expression
     * @return returns true if and only if the given expression is a literal a
     *         expression and it is true
     */
    // @ requires expr != null;
    public static boolean isTrueLit(Expr expr) {
        return isBooleanLiteral(expr, true);
    }

    /**
     * Determines whether a given expression is the false literal.
     * 
     * @param expr
     *            the inspected expression
     * @return returns true if and only if the given expression is a literal a
     *         expression and it is false
     */
    // @ requires expr != null;
    public static boolean isFalseLit(Expr expr) {
        return isBooleanLiteral(expr, false);
    }

    /**
     * Computes whether an expression contains a reference to a given variable.
     * 
     * @param varDecl
     *            the tested variable
     * @param e
     *            the tested expression
     * @return returns true if and only of <code>e</code> references
     *         <code>varDecl</code>
     */
    public static boolean usesVar(GenericVarDecl varDecl, Expr e) {
        GenericVarDeclVec eVars = getVars(e);
        return eVars.contains(varDecl);
    }

    static void remove(GenericVarDeclVec a, GenericVarDeclVec b) {
        for (int i = 0; i < b.size(); i++) {
            GenericVarDecl gvd = b.elementAt(i);
            a.removeElement(gvd);
        }
    }

    /**
     * Tests whether a given expression is using any of the given variables.
     * 
     * @param varDecls
     *            a <code>GenericVarDeclVec</code> value
     * @param e
     *            an <code>Expr</code> value
     * @return a <code>boolean</code> value
     */
    public static boolean usesAnyVar(GenericVarDeclVec varDecls, Expr e) {
        for (int i = 0; i < varDecls.size(); i++) {
            GenericVarDecl varDecl = varDecls.elementAt(i);
            if (usesVar(varDecl, e)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Fills the given vector with variable declarations for variables
     * referenced in the given expression.
     */
    static void getVars(ASTNode n, GenericVarDeclVec vec) {
        if (n instanceof VariableAccess) {
            VariableAccess va = (VariableAccess) n;
            GenericVarDecl varDecl = va.decl;

            if (!vec.contains(varDecl))
                vec.addElement(varDecl);
        } else {
            int childCount = n.childCount();
            for (int i = 0; i < childCount; i++) {
                Object child = n.childAt(i);
                if (child instanceof ASTNode) {
                    ASTNode childAST = (ASTNode) child;
                    getVars(childAST, vec);
                }
            }
            if (n instanceof QuantifiedExpr) {
                QuantifiedExpr q = (QuantifiedExpr) n;
                GenericVarDeclVec boundedVars = q.vars;
                remove(vec, boundedVars);
            }

        }
    }

    public static GenericVarDeclVec getVars(ASTNode n) {
        GenericVarDeclVec vec = GenericVarDeclVec.make();
        getVars(n, vec);
        return vec;
    }
    
    public static boolean isGround(ASTNode n) {
        return getVars(n).size() == 0;
    }

    public static boolean shareVariables(Expr e1, Expr e2) {
        GenericVarDeclVec vec1 = getVars(e1);
        GenericVarDeclVec vec2 = getVars(e2);
        boolean doIntersect = intersect(vec1, vec2);

        /*
         * reportln("Intersect test: " + doIntersect);
         * PredicateAbstraction.printlnExpr(e1);
         * PredicateAbstraction.printlnExpr(e2);
         */

        return doIntersect;
    }

    public static boolean shareVariables(ExprVec es, Expr e) {
        /*
         * reportln("== test for variable sharing ");
         * PredicateAbstraction.printlnExprVec(es); reportln(" and ");
         * PredicateAbstraction.printlnExpr(e);
         */

        for (int i = 0; i < es.size(); i++) {
            Expr e1 = es.elementAt(i);

            if (shareVariables(e, e1))
                return true;
        }
        return false;
    }

    public static boolean predContain(Expr pred, ExprVec predVec) {
        for (int i = 0; i < predVec.size(); i++) {
            if (isSame(predVec.elementAt(i), pred)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Adds a given expression to a given expression vector but only when it's
     * not already contained.
     * 
     * @param pred
     *            the expression to be added
     * @param predVec
     *            the vector in which to add
     */
    public static void setAdd(Expr pred, ExprVec predVec) {
        boolean alreadyThere = contains(predVec, pred);
        if (!alreadyThere) {
            predVec.addElement(pred);
        }
    }

    static void setAppend(ExprVec ev, ExprVec appendix) {
        for (int i = 0; i < appendix.size(); i++) {
            Expr e = appendix.elementAt(i);
            setAdd(e, ev);
        }
    }

    public static ExprVec join(ExprVec ev1, ExprVec ev2) {
        ExprVec retv = ExprVec.make();
        setAppend(retv, ev1);
        setAppend(retv, ev2);
        return retv;
    }

    /**
     * Creates a copy of the given expression vector but duplicated expressions
     * are included just once. The method <code>isSame</code> is used as the
     * equality test.
     */
    public static ExprVec removeDuplicates(ExprVec evec) {
        ExprVec cleanPredicates = ExprVec.make(evec.size());

        for (int i = 0; i < evec.size(); i++) {
            Expr e = evec.elementAt(i);
            setAdd(e, cleanPredicates);
        }

        return cleanPredicates;
    }

    /**
     * From a set of expression returns a subset of such expressions that do not
     * refer to the specified set of (irelevant) variables.
     * 
     * @param oldExprs
     *            the set to be filtered
     * @param nonRelevantVariables
     *            the set of (irelevant) variables
     * @return filtered expression set, if the given expression is
     *         <code>null</code> ther return value is null, otherwise it is
     *         non-null
     */
    public static ExprVec filterIrelevantExpressions(ExprVec oldExprs,
            GenericVarDeclVec nonRelevantVariables) {
        if (oldExprs == null) {
            return null;
        }

        ExprVec filteredExprs = ExprVec.make();

        for (int i = 0; i < oldExprs.size(); i++) {
            Expr oldExpr = oldExprs.elementAt(i);
            if (!AlgebraUtils.usesAnyVar(nonRelevantVariables, oldExpr)) {
                // the pattern doesn't refer to any of the irelevant variables
                filteredExprs.addElement(oldExpr); // it is added to the new
                                                    // set
            }

        }
        return filteredExprs;
    }

    /**
     * For a given quantified expression, the variables that are quantified over
     * are split into two sets according to whether they are relevant or
     * irrelevant to the inside of the quantified expression.
     * 
     * @param qe
     *            the quantified expression to be tested
     * @param relevantVars
     *            to this vector the relevant vars will be added
     * @param nonRelevantVars
     *            to this vector the irelevant vars will be added
     */
    //@ requires qe != null && relevantVars != null && nonRelevantVars != null;
    //@ ensures qe.vars.size() == relevantVars.size() + nonRelevantVars.size();
    public static void relevantVariablesSplit(QuantifiedExpr qe,
            GenericVarDeclVec relevantVars, GenericVarDeclVec nonRelevantVars) {
        Expr boundExpr = qe.expr;
        GenericVarDeclVec vars = qe.vars;

        for (int i = 0; i < vars.size(); i++) {
            GenericVarDecl varDecl = vars.elementAt(i);
            boolean isRelevant = AlgebraUtils.usesVar(varDecl, boundExpr);
            if (qe.rangeExpr != null) {
                if (AlgebraUtils.usesVar(varDecl, qe.rangeExpr))
                    isRelevant = true; // is this optimal?
            }

            GenericVarDeclVec addToVec;
            if (isRelevant) {
                addToVec = relevantVars;
            } else {
                addToVec = nonRelevantVars;
            }
            addToVec.addElement(varDecl);
        }
    }

    /**
     * Compares two expression vectors using <code>isSame</code> method to
     * compare the elements .
     */
    public static boolean isSame(ExprVec v1, ExprVec v2) {
        if (v1.size() != v2.size())
            return false;

        for (int i = 0; i < v1.size(); i++) {
            boolean areSame = isSame(v1.elementAt(i), v2.elementAt(i));
            if (!areSame) {
                return false;
            }
        }

        return true;
    }

    public static boolean isSameNullSafe(ExprVec p1, ExprVec p2) {
        if ((p1 == null && p2 != null) || (p1 != null && p2 == null)) {
            return false;
        } else {
            // either both non-null or both null
            if (p1 != null && p2 != null && !isSame(p1, p2))
                return false; // both non-null but different
        }
        return true;
    }

    public static boolean isSameNullSafe(Expr p1, Expr p2) {
        if ((p1 == null && p2 != null) || (p1 != null && p2 == null)) {
            return false;
        } else {
            // either both non-null or both null
            if (p1 != null && p2 != null && !isSame(p1, p2))
                return false; // both non-null but different
        }

        return true;
    }

    public static boolean isSame(Expr p1, Expr p2) {
        p1 = stripOffLabels(p1);
        p2 = stripOffLabels(p2);

        boolean retv;
        if (p1.getTag() != p2.getTag()) {
            retv = false;
        } else {
            if ((p1 instanceof VariableAccess)
                    && (p2 instanceof VariableAccess)) {
                VariableAccess va1 = (VariableAccess) p1;
                VariableAccess va2 = (VariableAccess) p2;
                retv = (va1.id).equals(va2.id);
            } else {
                if (p1 instanceof NaryExpr && p2 instanceof NaryExpr) {
                    NaryExpr n1 = (NaryExpr) p1;
                    NaryExpr n2 = (NaryExpr) p2;
                    retv = (n1.op == n2.op) && isSame(n1.exprs, n2.exprs);
                } else {
                    if (p1 instanceof TypeExpr && p2 instanceof TypeExpr) {
                        TypeExpr te1 = (TypeExpr) p1;
                        TypeExpr te2 = (TypeExpr) p2;
                        retv = (te1.eloc == te2.eloc)
                                && te1.type.equals(te2.type);
                    } else {
                        if (p1 instanceof QuantifiedExpr
                                && p2 instanceof QuantifiedExpr) {
                            QuantifiedExpr q1 = (QuantifiedExpr) p1;
                            QuantifiedExpr q2 = (QuantifiedExpr) p2;

                            retv = q1.quantifier == q2.quantifier
                                    && setEquals(q1.vars, q2.vars)
                                    && isSameNullSafe(q1.rangeExpr,
                                            q2.rangeExpr)
                                    && isSame(q1.expr, q2.expr);
                        } else {
                            if (p1 instanceof BinaryExpr
                                    && p2 instanceof BinaryExpr) {
                                BinaryExpr be1 = (BinaryExpr) p1;
                                BinaryExpr be2 = (BinaryExpr) p2;
                                retv = (be1.op == be2.op)
                                        && isSame(be1.left, be2.left)
                                        && isSame(be1.right, be2.right);
                            } else {
                                if (p1 instanceof LiteralExpr && p2 instanceof LiteralExpr) {
                                    LiteralExpr le1 = (LiteralExpr) p1;
                                    LiteralExpr le2 = (LiteralExpr) p2;
                                    if (le1.value == null)
                                        retv = le2.value == null;
                                    else 
                                        retv = le1.value.equals(le2.value);
                                    
                                } else {                              
                                    retv = p1.equals(p2);
                                }
                            }

                        }
                    }
                }
            }
        }

        /*
         * Debug print System.out.println("--- Comparing: ");
         * PredicateAbstraction.printExpr(p1); System.out.println(",\n");
         * PredicateAbstraction.printExpr(p2); System.out.println("\n");
         * 
         * if (retv) { System.out.println("---- Same"); } else {
         * System.out.println("---- Different"); } End of debug print
         */

        return retv;
    }
    
   
    static ExprVec remove(ExprVec ev, Expr e ) {
       ExprVec retv = ExprVec.make(ev.size());
       for (int i = 0; i < ev.size(); i++) {
           if (!isSame(ev.elementAt(i), e)) 
               retv.addElement(ev.elementAt(i));
       }
       return retv;
    }
    
    public static int flaSize(ASTNode node) {
        int size = 1;
        for (int i = 0; i < node.childCount(); i++) {
            Object child = node.childAt(i);

            if (child instanceof ASTNode) {
                size += flaSize((ASTNode) child);
            }
        }
        return size;
    }
    
    static Expr negSimple(Expr e) {
        if (isTrueLit(e))
            return GC.falselit;
        if (isFalseLit(e))
            return GC.truelit;
        
        return GC.not(e);
    }
    
    static Expr addFact(Expr fact, Expr e) {
        if (isSame(fact, e))
            return GC.truelit;
                    
        switch (e.getTag()) {
        case TagConstants.AND: {
            NaryExpr and = (NaryExpr) e;
            ExprVec conj = and.exprs;
            ExprVec retv = ExprVec.make(conj.size());
            for (int i = 0; i < conj.size(); i++) {
                Expr retvElement = addFact(fact, conj.elementAt(i));
                retv.addElement(retvElement);
            }
            return andSimple(retv);
        }
        case TagConstants.BOOLOR: {
            NaryExpr or = (NaryExpr) e;
            ExprVec oldVec = or.exprs;
            if (contains(oldVec, fact))
                return GC.truelit;
            else {
                ExprVec disj = ExprVec.make(oldVec.size());
                for (int i = 0; i < oldVec.size(); i++) {
                    Expr retvElement = addFact(fact, oldVec.elementAt(i));
                    disj.addElement(retvElement);
                }
                return GC.or(disj);
            }
        }
        case TagConstants.BOOLIMPLIES: {
            NaryExpr impl = (NaryExpr) e;
            Expr left = addFact(fact, impl.exprs.elementAt(0));
            Expr right = addFact(fact, impl.exprs.elementAt(1));            
            return implySimple(left, right);   
        }
        case TagConstants.BOOLNOT: {
            Expr neg = ((NaryExpr) e).exprs.elementAt(0);
            return negSimple(addFact(fact, neg));
        }
        case TagConstants.FORALL: {
            QuantifiedExpr qe = (QuantifiedExpr) e;
            if (!usesAnyVar(qe.vars, e)) {
                Expr newBound = addFact(fact, qe.expr);
                Expr retvQE = GC.quantifiedExpr(qe.sloc, qe.eloc, qe.getTag(), qe.vars, qe.rangeExpr, newBound, qe.nopats, qe.pats);
                return pruneQuantifiedExpr(retvQE);
            }
        }
        default: return e;
        }
        
    }
    
    static Expr implyFromAnds(ExprVec leftConj, ExprVec rightConj) {
        if (leftConj.size() == 0) {
            return andSimple(rightConj);
        }
        
        return implySimple(andSimple(leftConj), andSimple(rightConj));   
    }
    
    public static Expr implySimple(Expr left, Expr right) {
        if (isTrueLit(right))
            return GC.truelit;
        
        if (isFalseLit(left))
            return GC.truelit;
        
        return GC.implies(left, right);
    }
    
    static Expr pruneImplication(Expr left, Expr right) {
        ExprVec lList = removeDuplicates(flattenAnd(left));
        ExprVec rList = removeDuplicates(flattenAnd(right));
        
        rList = difference(rList, lList);
        
        if (rList.size() == 0) {
            return GC.truelit;
        }
        
        Expr rh = andSimple(rList);
        for (int i = 0; i < lList.size(); i++) {
            Expr f = lList.elementAt(i);
            rh = addFact(f, rh);
        }
        
        return implySimple(andSimple(lList), rh);       
    }
    
    public static Expr pruneImplications(Expr expr) {
        Expr pred = stripOffLabels(expr);

        if (pred.getTag() == TagConstants.BOOLIMPLIES) {
            NaryExpr ne = (NaryExpr) pred;
            ExprVec ev = ne.exprs;
            if (ev.size() == 2) {
                Expr left = pruneImplications(ev.elementAt(0));
                Expr right = pruneImplications(ev.elementAt(1));
                return pruneImplication(left, right);
//                
//                if (right.getTag() == TagConstants.BOOLOR) {
//                    ExprVec rOrs = ((NaryExpr) right).exprs;
//                    ExprVec retvOrs = ExprVec.make(rOrs.size());
//                    for (int i = 0 ; i < rOrs.size(); i++) {
//                        Expr cImpl = GC.implies(left, rOrs.elementAt(i));
//                        retvOrs.addElement(pruneImplications(cImpl));
//                    }
//                    return GC.or(retvOrs);
//                } else {                
//                    return pruneImplication(left, right);
//                }
            }
        } else {
            if (pred instanceof NaryExpr) {
                NaryExpr ne = (NaryExpr) pred;
                ExprVec ev = ne.exprs;
                ExprVec newEvec = ExprVec.make(ev.size());
                for (int i = 0; i < ev.size(); i++) {
                    Expr prunedE = pruneImplications(ev.elementAt(i));
                    newEvec.addElement(prunedE);
                }
                NaryExpr retv = NaryExpr.make(ne.sloc, ne.eloc, ne.op,
                        ne.methodName, newEvec);

                if (pred.getTag() == TagConstants.BOOLAND
                        || pred.getTag() == TagConstants.BOOLOR) {
                    pruneAndOrNary(retv);
                }

                return retv;
            } else {
                if (pred instanceof QuantifiedExpr) {
                    QuantifiedExpr qe = (QuantifiedExpr) pred;
                    Expr boundExpr = qe.expr;

                    Expr prunedBoundExpr = pruneImplications(boundExpr);

                    QuantifiedExpr prunedQuantExpr = QuantifiedExpr.make(
                            qe.sloc, qe.eloc, qe.quantifier, qe.vars,
                            qe.rangeExpr, prunedBoundExpr, qe.nopats, qe.pats);
                    return pruneQuantifiedExpr(prunedQuantExpr);
                }
            }

        }

        return pred;

    }
    
    public static Expr vytkniAndFromOr_plunge(Expr o) {    
        int tag = o.getTag();
        if (tag == TagConstants.BOOLOR)
            return vytkniAndFromOr(o);

        if (o instanceof NaryExpr) {
            NaryExpr ne = (NaryExpr) o;
            ExprVec oldVec = ne.exprs;
            ExprVec newVec = ExprVec.make(oldVec.size());
            for (int i = 0; i < oldVec.size(); i++) {
                newVec.addElement(vytkniAndFromOr_plunge(oldVec.elementAt(i)));
            }

            NaryExpr retv = NaryExpr.make(ne.sloc, ne.eloc, ne.op, ne.methodName, newVec);
            
            return retv;
        }
        
        return o;
    }

    public static Expr stripOffLabelsDeep(Expr e) {
        e = stripOffLabels(e);
        if (e instanceof NaryExpr) {
            NaryExpr ne = (NaryExpr) e;
            ExprVec oldVec = ne.exprs;
            ExprVec newVec = ExprVec.make(oldVec.size());
            for (int i = 0; i < oldVec.size(); i++) {
                newVec.addElement(stripOffLabelsDeep(oldVec.elementAt(i)));
            }

            NaryExpr retv = NaryExpr.make(ne.sloc, ne.eloc, ne.op,
                    ne.methodName, newVec);

            return retv;
        }
        
        if (e instanceof QuantifiedExpr) {
            QuantifiedExpr qe = (QuantifiedExpr) e;
            return QuantifiedExpr.make(qe.sloc, qe.eloc, qe.quantifier, qe.vars, qe.rangeExpr, stripOffLabelsDeep(qe.expr), qe.nopats, qe.pats);            
        }
        
        return e;
    }

    
    public static Expr vytkniAndFromOr(Expr o) {
        if (o.getTag() != TagConstants.BOOLOR)
            return o;
        
        //printExpression("vyknuti: ", o);
        
        NaryExpr or = (NaryExpr) o;
        ExprVec disj = or.exprs;
        if (disj.size() != 2)
            return o;
        
        ExprVec d0 = flattenAnd(disj.elementAt(0));
        ExprVec d1 = flattenAnd(disj.elementAt(1));
        ExprVec common = findCommon(d0, d1);
        
        if (common.size() > 0) {
            Expr orPart = GC.or(andSimple(difference(d0, common)), andSimple(difference(d1, common)));
            
            return GC.and(andSimple(common), normalizeOr(orPart));
        } else {
            return o;  
        }
        
        
    }
    
    static boolean isSymmetricBinary(int tag) {
        return (tag == TagConstants.ANYEQ) || 
               (tag == TagConstants.INTEGRALEQ) || (tag == TagConstants.FLOATINGEQ) || 
               (tag == TagConstants.INTEGRALEQ) ||
               (tag == TagConstants.REFEQ);    
    }
    
    static Expr normalizeIff(Expr e) {
        if (e.getTag() != TagConstants.BOOLEQ) 
            return e;
        
        NaryExpr ne = (NaryExpr) e;
        
        Expr e0 = ne.exprs.elementAt(0);
        Expr e1 = ne.exprs.elementAt(1);
        if (isSame(e0, e1)) {
            return GC.truelit;
        }
        
        if (isTrueLit(e0)) {
            return e1;
        }
        
        if (isTrueLit(e1)) {
            return e0;
        }
        
        return e;
    }
    
    static Expr normalizeEq(Expr p) {
        int tag = p.getTag();
        if (isSymmetricBinary(tag)) {
            NaryExpr eq = (NaryExpr) p;
            ExprVec ev = eq.exprs;
            Expr e0 = ev.elementAt(0);
            Expr e1 = ev.elementAt(1);
            if (isSame(e0, e1))
                return GC.truelit;
         }
        
        return p;
    }
    
    public static Expr normalizeOr(Expr pred) {
        if (pred.getTag() != TagConstants.BOOLOR)
            return pred;
        
        ExprVec disj = removeDuplicates(((NaryExpr) pred).exprs);
        if (contains(disj, GC.truelit)) {
            return GC.truelit;
        }
        
        if (containsComplementary(disj)) {
            return GC.truelit;
        }
        
        return GC.or(disj);
    }
    
    public static Expr normalizeAnd(Expr e) {
        if (e.getTag() != TagConstants.BOOLAND)
            return e;

        ExprVec conj = removeDuplicates(((NaryExpr) e).exprs);
        conj = remove(conj, GC.truelit);
        if (containsComplementary(conj)) {
            return GC.falselit;
        }
        return andSimple(conj);
    }
    
    static Expr normalize_deep(Expr e) {   
        e = normalizeOr(e);
        e = normalizeEq(e);
        e = normalizeAnd(e);
        e = normalizeIff(e);

        if (e instanceof NaryExpr) {
            NaryExpr ne = (NaryExpr) e;
            ExprVec oldVec = ne.exprs;
            ExprVec newVec = ExprVec.make(oldVec.size());
            for (int i = 0; i < oldVec.size(); i++) {
                newVec.addElement(normalize_deep(oldVec.elementAt(i)));
            }

            return NaryExpr.make(ne.sloc, ne.eloc, ne.op, ne.methodName, newVec);
        }
        
        if (e instanceof QuantifiedExpr) {
            QuantifiedExpr qe = (QuantifiedExpr) e;
            qe =  QuantifiedExpr.make(qe.sloc, qe.eloc, qe.quantifier, qe.vars, qe.rangeExpr, normalize_deep(qe.expr), qe.nopats, qe.pats);
            return pruneQuantifiedExpr(qe);
        }
        
        return e;
    }
    
    public static Expr grind(Expr pred) {
       pred = stripOffLabelsDeep(pred);
       Expr oldPred = pred;
       do {
           oldPred = pred;
           pred = removeLetExpressions(pred);
           pred = vytkniAndFromOr_plunge(pred);
           pred = pruneImplications(pred);
           pred = pruneQuantifiedExpr(pred);
           pred = normalize_deep(pred);
       } while (!isSame(oldPred, pred));
       return pred;
    }
    
    public static ExprVec findCommon(ExprVec e1, ExprVec e2) {
      ExprVec common = ExprVec.make();
      for (int i = 0; i < e1.size(); i++) {
          Expr ex1 = e1.elementAt(i);
          if (contains(e2, ex1))
              common.addElement(ex1);
      }
      return common;
    }
    
    
    /**
     * Removes elements that occur in both given lists from them.
     * @param e1
     * @param e2
     */
    public static /*@non_null@*/ExprVec removeCommon(ExprVec e1, ExprVec e2) {
        int i1 = 0;
        ExprVec common = ExprVec.make();
        while (i1 < e1.size()) {
            int i2 = 0;
            
            while (i2 < e2.size() && i1 < e1.size()) {
                Expr ex1 = e1.elementAt(i1);
                Expr ex2 = e2.elementAt(i2);
                if (isSame(ex1, ex2)) {
                    e1.removeElementAt(i1);
                    e2.removeElementAt(i2);
                    common.addElement(ex1);
                    i2 = 0;
                } else {
                    i2++;
                }
            }
            i1++;
        }
        return common;
    }
    
    public static void flattenAnd(Expr e, ExprVec monomial) {
        e = AlgebraUtils.stripOffLabels(e);

        if (e.getTag() == TagConstants.BOOLAND) {
            NaryExpr ne = (NaryExpr) e;
            ExprVec ev = ne.exprs;
            for (int i = 0; i < ev.size(); i++)
                flattenAnd(ev.elementAt(i), monomial);
        } else {
            monomial.addElement(e);
        }
    }
    
    public static ExprVec flattenAnd(Expr e) {
        ExprVec varVec = ExprVec.make();
        flattenAnd(e, varVec);
        return varVec;
    }

    static ExprVec computeDependent(Expr e, ExprVec tested) {
        ExprVec depTest = ExprVec.make(1);
        depTest.addElement(e);

        ExprVec dependent = ExprVec.make();

        ExprVec toBeSplit = tested;

        while (depTest.size() > 0 && toBeSplit.size() > 0) {
            ExprVec currentDependent = ExprVec.make();
            ExprVec currentIndependent = ExprVec.make();

            dependencySplit(depTest, toBeSplit, currentDependent,
                    currentIndependent);

            dependent.append(currentDependent);
            toBeSplit = currentIndependent;
            depTest = currentDependent;
        }

        return dependent;
    }

    static void dependencySplit(ExprVec depTest, ExprVec initialVec,
            ExprVec dependent, ExprVec independent) {
        /*
         * reportln("== splitting ");
         * PredicateAbstraction.printlnExprVec(initialVec); reportln(" by ");
         * PredicateAbstraction.printlnExprVec(depTest);
         */

        for (int i = 0; i < initialVec.size(); i++) {
            Expr testedExpr = initialVec.elementAt(i);
            ExprVec addTo;
            if (AlgebraUtils.shareVariables(depTest, testedExpr)) {
                addTo = dependent;
            } else {
                addTo = independent;
            }

            addTo.addElement(testedExpr);
        }
    }

    // boolean contains(GenericVarDecl varDec, GenericVarDeclVec vect) {
    // }

    
    public static Expr pruneQuantifiedExpr(Expr e) {
        if (e instanceof QuantifiedExpr) {
            QuantifiedExpr qe = (QuantifiedExpr) e;
            return pruneQuantifiedExpr(qe);
        }
        else
            return e;
    }
    /**
     * Removes quantifiers that are not used inside the quantified expression.
     */
    //@ requires qe != null;
    public static Expr pruneQuantifiedExpr(QuantifiedExpr qe) {
        Expr boundExpr = qe.expr;
        Expr rangeExpr = qe.rangeExpr;
      
        // get the relevant and invariant variables that is quantified over
        GenericVarDeclVec relevantVars = GenericVarDeclVec.make();
        GenericVarDeclVec nonRelevantVars = GenericVarDeclVec.make();

        AlgebraUtils.relevantVariablesSplit(qe, relevantVars, nonRelevantVars);

        // filter out the relevant pats and nopats
        ExprVec relevantPats = AlgebraUtils.filterIrelevantExpressions(qe.pats,
                nonRelevantVars);
        ExprVec relevantNoPats = AlgebraUtils.filterIrelevantExpressions(
                qe.nopats, nonRelevantVars);

        Expr retv;

        if (relevantVars.size() > 0) {
            // create a new quantified expr with only the relevant vars, if there are any
            retv = QuantifiedExpr.make(qe.sloc, qe.eloc, qe.quantifier,
                    relevantVars, rangeExpr, boundExpr, relevantPats,
                    relevantNoPats);
        } else {
            // qe didn't quantify over anything relevant, strip off the
            // quantifier
            retv = boundExpr;
            if (qe.rangeExpr != null) {
                // if there was a range expression, translate it to a
                // implication
                retv = GC.implies(qe.rangeExpr, retv);
            }
        }

        return retv;
    }

    public static boolean isNaryAssocComutative(Expr e) {
        if (e instanceof NaryExpr) {
            NaryExpr nex = (NaryExpr) e;
            return isAssocComutative(nex);
        } else {
            return false;
        }
    }

    public static boolean isAssocComutative(NaryExpr nex) {
        return nex.getTag() == TagConstants.BOOLAND
                || nex.getTag() == TagConstants.BOOLOR;
    }


    public static void printExprVec(String s, ExprVec ev) {
      System.out.println(s);
      System.out.print('[');
      for (int i = 0; i < ev.size(); i++) {
          printExpression(ev.elementAt(i));
          System.out.print(i == ev.size() - 1 ? "]": ", " );
      }         
      System.out.println();
    }
    
    static String getDescr(int tag) {
        String op = null;
        switch (tag) {
        case TagConstants.BOOLIMPLIES:
            op = "IMPLIES";
            break;
        case TagConstants.BOOLAND:
        case TagConstants.BOOLANDX:
            op = "AND";
            break;
        case TagConstants.BOOLOR:
            op = "OR";
            break;
        case TagConstants.BOOLNOT:
            op = "NOT";
            break;
        case TagConstants.BOOLEQ:
            op = "IFF";
        }

        return op;
    }
    
    static String indent(int level) {
        String retv = "";
        for (int i = 0; i < level; i++) retv += ' ';
        return retv;
    }
    
    // only debugging purposes
    public static void printExpression(String s, Expr e) {
        System.out.println(s);
        printExpression(e);
        
        System.out.println();
    }

    // only debugging purposes
    public static void printExpression(Expr e) {
        printExpression(e, 0);        
    }

    public static void printExpression(Expr e, int level) {
        if ((getDescr(e.getTag()) != null)  && e instanceof NaryExpr) {
            System.out.println(indent(level) + getDescr(e.getTag()) + '(');
            
            ExprVec exprs = ((NaryExpr) e).exprs;
            for (int i = 0; i < exprs.size(); i++) {
                printExpression(exprs.elementAt(i), level+1);
                if (i == exprs.size() - 1) {
                    System.out.print(')');            
                }
                else {
                    System.out.println();
                }
            }            
      }  else {
          int tag = e.getTag();
          if (tag == TagConstants.FORALL || tag == TagConstants.EXISTS) {
              QuantifiedExpr qe = (QuantifiedExpr) e;
              String descr = tag ==TagConstants.FORALL ? "FORALL" : "EXISTS";
              System.out.print( indent(level) + '(' + descr + " (");
              for (int i = 0; i < qe.vars.size(); i++) {
                  System.out.print(Atom.printableVersion(UniqName.variable(qe.vars.elementAt(i))));
                  if (i == qe.vars.size() -1) {
                      System.out.println(')');
                  } else {
                      System.out.print(' ');
                  }                  
              }
              if (qe.rangeExpr != null && !isTrueLit(qe.expr)) printExpression(qe.rangeExpr, level + 1);
              printExpression(qe.expr, level + 1);
              System.out.print(')');
          } else {    
          System.out.print(indent(level));
          VcToString.computeTypeSpecific(e, System.out);
          }
      }        
    }

    

}
