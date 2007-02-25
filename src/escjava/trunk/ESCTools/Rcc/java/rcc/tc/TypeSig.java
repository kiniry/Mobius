/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.LinkedList;
import java.util.List;

import javafe.ast.CompilationUnit;
import javafe.ast.Expr;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.PrettyPrint;
import javafe.ast.ThisExpr;
import javafe.ast.TypeDecl;
import javafe.tc.Env;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import rcc.ast.EqualsASTNoDecl;

/**
 * NOTE Below I use `parameters' as a shorthand for `formal parameters'
 *      and `arguments' as a shorthand for `actual arguments'.
 *      
 * In general there is one <code>TypeSig</code> object for each type
 * defined in the input Java files. In order to implement types with
 * ghost parameters (kind of dependent types?) we maintain families
 * of TypeSig-s for each type defined in the input Java files as follows.
 * 
 * If in the input there is a class declaration
 *   class C<ghost l> { ... }
 * then we create a TypeSig object known as the `default instantiation' 
 * of class C. Its <code>defaultInstantiation</code> field points to itself; its 
 * <code>expressions</code> field contains {l}. If a field is declared as
 *   C<o> f;
 * then we create a TypeSig object whose <code>defaultInstantiation</code> field
 * points to the default instantiation and whose <code>expressions</code>
 * field stores {o}.
 *
 * Each instantiation has the same
 *   CU (compilation unit),
 *   enclosingEnv,
 *   hiddenfields, ??
 *   fields,       ??
 *   methods,      ??
 *   member,
 *   myTypeDecl, and
 *   packageName
 * fields as the default instantiation. It may have a different
 *   simpleName (for debug),
 *   state,        ??
 *   enclosingType,
 *   superClass.
 *
 * The default instantiation shall not be used while doing flow insensitive
 * checks. A class that has no generic parameter has a default instantiation
 * and exactly one other instantiation (with an empty |expressions| list)
 * which is the one to be used by <code>FlowInsensitiveChecks</code>. 
 *
 * We provide methods to figure out if a field is a ghost field and, if so,
 * what is the expression it is instantiated with in this TypeSig.
 * 
 * The default instantiation is created by JavaFE by calling 
 * Types.makeTypeSigInstance. (TODO We need a method to make sure that
 * parameters end up somehow in the default instantiation.) 
 * Other instantiations are created when type names with arguments are
 * resolved. No two TypeSig objects have o1.generic == o2.generic and
 * o1.expressions == o2.expressions, where the latter equality is syntactical.
 * To do this, we keep references from the default instantiation x to all
 * the other TypeSig object y for which y.generic == x in the list
 * <code>nonDefaultInstantiations</code>.
 * 
 * TODO do I need to override isSubTypeOf to handle array elem guards?
 * 
 * @see javafe.tc.TypeSig, rcc.tc.PrepTypeDeclaration 
 * @see rcc.tc.FlowInsensitiveChecks
 */
public class TypeSig extends javafe.tc.TypeSig {
    /**
     * For default instantiations this holds the formal parameters.
     * All elements must be FieldAccess.
     * For other instantiations this holds the actual arguments.
     * All elements must be ThisExpr or FieldAccess.
     */
    private ExprVec expressions;

    /**
     * Points to the default instantiation of this type signature.
     * For the default instantiation <code>generic==this</code>.
     */
    private TypeSig defaultInstantiation;
    
    /**
     * This is non-null iff this is a default instantiation and contains
     * references to all the other instantiations.
     */
    private List nonDefaultInstantiations;  
    
    /**
     * Used to compare syntactically two arguments.
     */
    private static final EqualsASTNoDecl eq = new EqualsASTNoDecl();


    /*
     * All constructors of javafe.tc.TypeSig have counterparts here that
     * also initialize |expressions| and |generic|.
     */
    public TypeSig(String simpleName, Env enclosingEnv, TypeDecl decl) {
        super(simpleName, enclosingEnv, decl);
        initDefaultInstantiation();
    }
    public TypeSig(
        String[] packageName, 
        String simpleName, 
        TypeDecl decl, 
        CompilationUnit CU
    ) {
        super(packageName, simpleName, decl, CU);
        initDefaultInstantiation();
    }
    public TypeSig(
        String[] packageName, 
        String simpleName, 
        TypeSig enclosingType, 
        TypeDecl decl, 
        CompilationUnit CU
    ) {
        super(packageName, simpleName, enclosingType, decl, CU);
        initDefaultInstantiation();
    }
    
    private void initDefaultInstantiation() {
        expressions = ExprVec.make(); // shall be filled later 
        defaultInstantiation = this;
        nonDefaultInstantiations = new LinkedList();
    }
    
    private TypeSig() {
        super(null, null, null); // does this work?
    }
    
    /**
     * If <code>typeName</code> has a <code>typeArgumentDecoration</code>
     * then we return the instantiation corresponding to those arguments.
     * Otherwise we return this.
     * 
     * This method must be called only for the default instantiation. 
     * 
     * @param arguments The arguments for which we want the instantiation.
     * @return The signature corresponding to <code>typeName</code>.
     */
    public TypeSig getInstantiation(ExprVec arguments) {
        Assert.precondition(defaultInstantiation == this);
        
        // Check that arguments are either ThisExpr or FieldAccess.
        int i, j;
        for (i = 0; i < arguments.size(); ++i) {
            Expr expr = arguments.elementAt(i);
            if (expr instanceof ThisExpr) continue;
            if (expr instanceof FieldAccess) continue;
            ErrorSet.fatal("A ghost argument must be a final Object field.");
            // TODO check the 'final Object' bit.
            return null;
        }
        
        // Check that the number of arguments is the same as the number
        // of parameters.
        if (arguments.size() != defaultInstantiation.expressions.size()) {
            ErrorSet.fatal("The number of ghost arguments does not match "
                + "the number of parameters.");
            return null;
        }
        
        // Look at all existent instantiations one by one and compare
        // the arguments syntactically, ignoring declarations.
        for (j = 0; j < nonDefaultInstantiations.size(); ++j) {
            TypeSig inst = (TypeSig)nonDefaultInstantiations.get(j);
            for (i = 0; i < arguments.size(); ++i) {
                Expr arg = arguments.elementAt(i);
                Expr param = inst.expressions.elementAt(i);
                if (!eq.equals(arg, param)) break;
            }
            if (i < arguments.size()) return inst; // found a match
        }
        
        // No instantiation is suitable. I'll have to make one.
        // TODO enclosing Type, superClass?
        String newSimpleName
            = simpleName + "<" + PrettyPrint.inst.toString(arguments) + ">"; 
        TypeSig newInst = new TypeSig(newSimpleName, enclosingEnv, myTypeDecl);
        newInst.expressions = arguments.copy();
        newInst.defaultInstantiation = this;
        // we are likely to look for the same instance soon, so insert in front
        nonDefaultInstantiations.add(0, newInst);
        
        Info.out("I have created the instantiation " + newSimpleName);
        
        return newInst;
    }
    
    /**
     * Given a formal parameter, return the actual argument or null if
     * there isn't such. So null is returned for example when this is
     * a default instantiation and when <code>formal</code> is not
     * a ghost field but a normal one.
     */
    public Expr getActual(Expr formal) {
        if (defaultInstantiation == this) return null;
        
        // Identify the position of the parameter.
        int pos;
        ExprVec formals = defaultInstantiation.expressions;
        for (pos = 0; pos < formals.size(); ++pos) {
            if (eq.equals(formal, formals.elementAt(pos))) break;
        }
        if (pos == formals.size()) return null; // no such formal param
        
        // Return the actual argument.
        return expressions.elementAt(pos);
    }
    
}
