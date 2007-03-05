/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.LinkedList;
import java.util.List;

import javafe.ast.CompilationUnit;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.FieldDeclVec;
import javafe.ast.Identifier;
import javafe.ast.MethodDeclVec;
import javafe.ast.PrettyPrint;
import javafe.ast.ThisExpr;
import javafe.ast.TypeDecl;
import javafe.tc.Env;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import rcc.Dbg;
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
 * TODO check whether two formal parameters have the same name and
 *      report a fatal(?) error if so
 * 
 * @see javafe.tc.TypeSig, rcc.tc.PrepTypeDeclaration 
 * @see rcc.tc.FlowInsensitiveChecks
 */
public class TypeSig extends javafe.tc.TypeSig {
    /**
     * This holds the formal paramters.
     */
    private FieldDeclVec parameters;
    
    /**
     * This holds the actual arguments.
     * All elements must be either ThisExpr or FieldAccess.
     */
    private ExprVec arguments;

    /**
     * Points to the default instantiation of this type signature.
     * For the default instantiation <code>generic==this</code>.
     */
    private TypeSig defaultInstantiation;

    //@invariant parameters == defaultInstantiation.parameters;
    //@invariant this != defaultInstantiation <==> arguments != null
    
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
        parameters = FieldDeclVec.make(); // shall be filled later
        arguments = null;
        defaultInstantiation = this;
        nonDefaultInstantiations = new LinkedList();
        Dbg.o("create default TypeSig for " + simpleName);
    }

    /**
     * This (huge) constructor initializes an instantiation.
     * (Basically, it does a shallow copy. It is quite ugly and risky
     * but I couldn't think of a better way that works with JavaFE.)
     * TODO how to handle the superClass field? 
     */
    private TypeSig(
        CompilationUnit CU,
        Env enclosingEnv,
        TypeSig enclosingType,
        FieldDeclVec fields,
        FieldDeclVec hiddenfields,
        boolean member,
        MethodDeclVec methods,
        TypeDecl myTypeDecl,
        String[] packageName,
        String simpleName,
        int state,
        ExprVec arguments,
        TypeSig defaultInstantiation
    ) {
        super(
            packageName,
            simpleName,
            enclosingType,
            myTypeDecl,
            CU
        );
        this.enclosingEnv = enclosingEnv;
        this.fields = fields;
        this.member = member;
        this.methods = methods;
        this.state = state; // TODO is this right?
        this.arguments = arguments;
        this.defaultInstantiation = defaultInstantiation;
    }
    
    public boolean hasFormals() {
        return defaultInstantiation.parameters != null;
    }
    
    public void resetFormals() {
        defaultInstantiation.parameters = FieldDeclVec.make();
    }
    
    public void addFormal(FieldDecl formal) {
        Dbg.o("add formal parameter to (default) TypeSig " + simpleName, formal);
        defaultInstantiation.parameters.addElement(formal);
    }
    
    /**
     * Are we a normal instance? (As opposed to the default one.)
     */
    public boolean isInstance() {
        return this != defaultInstantiation;
    }
    
    /**
     * We return the instantiation that has <code>exprs</code> as arguments.
     * 
     * This method must be called only for the default instantiation.
     * TODO Should I make this callable for instantiations too? 
     */
    public TypeSig getInstantiation(ExprVec exprs) {
        int i, j;
        Assert.precondition(defaultInstantiation == this);
        if (exprs == null) exprs = ExprVec.make();

        // These will become ThisExpr or FieldAccess later:
        // FlowInsensitiveChecks will do that. TODO provide access.
        
        // Check that the number of arguments is the same as the number
        // of parameters.
        if (exprs.size() != parameters.size()) {
            ErrorSet.fatal("The number of ghost arguments does not match "
                + "the number of parameters.");
            return null;
        }
        
        // Look at all existent instantiations one by one and compare
        // the arguments syntactically, ignoring declarations.
        for (j = 0; j < nonDefaultInstantiations.size(); ++j) {
            TypeSig inst = (TypeSig)nonDefaultInstantiations.get(j);
            for (i = 0; i < exprs.size(); ++i) {
                Expr arg1 = exprs.elementAt(i);
                Expr arg2 = inst.arguments.elementAt(i);
                if (!eq.equals(arg1, arg2)) break;
            }
            if (i == exprs.size()) return inst; // found a match
        }
        
        // No instantiation is suitable. I'll have to make one.
        // TODO enclosing Type, superClass?
        String newSimpleName
            = simpleName + "<" + PrettyPrint.inst.toString(exprs) + ">";
        Dbg.o("create instantiation TypeSig " + newSimpleName);
        TypeSig newInst = new TypeSig(
            CU,
            enclosingEnv,
            (TypeSig)enclosingType,
            fields,
            hiddenfields,
            member,
            methods,
            myTypeDecl,
            packageName,
            newSimpleName,
            state,
            exprs.copy(),
            this);
        // we are likely to look for the same instance soon, so insert in front
        nonDefaultInstantiations.add(0, newInst);

        Info.out("I have created the instantiation " + newSimpleName);
        
        return newInst;
    }
    
    /**
     * Given a formal parameter, return the actual argument or null if
     * there isn't such. So null is returned for example when this is
     * a default instantiation, and is also returned when <code>formal</code>
     * is not a ghost field but a normal one.
     * 
     * TODO use a hashtable for this
     * TODO can I really rely on string comparisons?
     */
    public Expr getActual(String formalName) {
        if (formalName == null) return null;
        Dbg.o("searching for the actual corresponding to " + formalName);
        if (defaultInstantiation == this) return null;
        int pos = getFormalPosition(formalName);
        if (pos < 0) return null;
        Expr result = arguments.elementAt(pos);
        Dbg.o("..the argument is", result);
        return result;
    }
    
    /**
     * Given a <code>formalName</code> returns its field declaration
     * if ther is one or null otherwise. In particular this method
     * always returns null if this is not the default instantiation.
     */
    //@ defaultInstantiation != this ==> \return == null;
    public FieldDecl getFormal(String formalName) {
        if (formalName == null) return null;
        if (defaultInstantiation != this) return null;
        int pos = getFormalPosition(formalName);
        if (pos < 0) return null;
        return parameters.elementAt(pos);
    }
    
    /**
     * Lookup the <code>formalName</code> in 
     * <code>defaultInstantion.parameters</code> and return the index,
     * or -1 if not found. 
     */
    private int getFormalPosition(String formalName) {
        int pos;
        for (pos = 0; pos < defaultInstantiation.parameters.size(); ++pos) {
            FieldDecl fd = defaultInstantiation.parameters.elementAt(pos);
            if (formalName.equals(fd.id.toString())) return pos; 
        }
        return -1;
    }

    /**
     * If <code>e</code> is a simple field access then it returns the identifier.
     * Otherwise it returns null.
     * 
     * If the expression is represents "x" in the source then we return the
     * string "x". If the expression represents "this.x" then we return the
     * string "x". If the expression represents "this", "x.y", or "this.x.y" 
     * then we return null. For any other type of expression we also return null.
     */
    public String getFormalName(Expr e) {
        if (!(e instanceof FieldAccess)) return null;
        FieldAccess fa = (FieldAccess)e;
        if (fa.od != null) {
            if (!(fa.od instanceof ExprObjectDesignator)) return null;
            ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
            if (!(eod.expr instanceof ThisExpr)) return null;
        }
        return fa.id.toString();
    }
    
    /**
     * Override. When we are in an annotation we also consult formal 
     * parameters declarations, and consider them as fields.
     */
    public boolean hasField(Identifier id) {
        if (super.hasField(id)) return true;
        if (!FlowInsensitiveChecks.inAnnotation) return false;
        return getFormalPosition(id.toString()) >= 0;
    }
    
    /**
     * Override. TODO.
     */
    public javafe.tc.TypeSig lookupType(
        javafe.tc.TypeSig caller, 
        Identifier id, 
        int loc
    ) {
        return super.lookupType(caller, id, loc);
    }
}
