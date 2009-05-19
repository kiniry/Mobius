package mobius.directVCGen.translator;

import java.util.HashSet;
import java.util.Set;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ObjectType;

import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
import javafe.ast.ClassDecl;
import javafe.ast.Expr;
import javafe.ast.FieldAccess;
import javafe.ast.MethodInvocation;
import javafe.ast.PrimitiveType;
import javafe.ast.RoutineDecl;
import javafe.ast.Type;
import javafe.ast.UnaryExpr;
import javafe.ast.VariableAccess;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.vcgen.ABasicVisitor;
import escjava.ast.CondExprModifierPragma;
import escjava.ast.EverythingExpr;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.TagConstants;
import escjava.tc.FlowInsensitiveChecks;
import escjava.tc.TypeSig;



/**
 * @author Claudia Brauchli (claudia@vis.ethz.ch)
 * @author Hermann Lehner (hermann.lehner@inf.ethz.ch)
 * @author Julien Charles (julien.charles@inria.fr)
 *
 */
final class VisibleTypeCollector extends ABasicVisitor {

  private final Set<Type> fTypeSet = new HashSet<Type>();

  private boolean fAssign;
  private boolean fEverything;
  
  
  /** */
  private VisibleTypeCollector() { }


  @Override
  public Object visitClassDecl(final /*@non_null*/ ClassDecl x, final Object o) {
    fTypeSet.add(TypeSig.getSig(x));
    //should never be called
    return visitTypeDecl(x, null);
  }

  @Override
  public Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, final Object o) {
    fAssign = false;
    visitASTNode(x, o); 
    if (fEverything) {
      fTypeSet.clear();
    }
    return null;
  }

  
  /**
   * We also want to collect all assignable types of a method invocation.
   */
  public /*@non_null*/ Object visitMethodInvocation(
                                            final /*@non_null*/ MethodInvocation x, 
                                            final Object o) {
    //add assignable pragma types to fTypeSet   
    for (int i = 0; i < x.decl.pmodifiers.size(); i++) {
      if (x.decl.pmodifiers.elementAt(i).getTag() == TagConstants.MODIFIESGROUPPRAGMA) {
        final ModifiesGroupPragma modi = (ModifiesGroupPragma) x.decl.pmodifiers.elementAt(i);
        CondExprModifierPragma assigPragma = null;
        for (int j = 0; j < modi.items.size(); j++) {
          assigPragma = modi.items.elementAt(j);
          if (assigPragma.expr instanceof FieldAccess) {
            final Type type2 = FlowInsensitiveChecks.getType(assigPragma.expr);
            fTypeSet.add(type2);
          }
          else if (assigPragma.expr instanceof EverythingExpr) {
            fEverything = true; 
            break;
          }
        }
      }
    }
    
    return null;
  }
  

  @Override
  public Object visitVariableAccess(final /*@non_null*/ VariableAccess x, 
                                                  final Object o) {
    if (fAssign) {
      final Type type = FlowInsensitiveChecks.getType(x);
      if (!(type instanceof PrimitiveType)) {
        fTypeSet.add(type);
      }
    }
    return null;
  }

  @Override
  public Object visitFieldAccess(final /*@non_null*/ FieldAccess x, 
                                               final Object o) {
    final Type type = x.od.type();
    if (!(type instanceof PrimitiveType) && fAssign) {
      fTypeSet.add(type);
    }

    fAssign = false;
    ((ASTNode)x.od.childAt(0)).accept(this, o);
    return null;
  }



  @Override
  public Object visitBinaryExpr(final BinaryExpr expr, final Object o) {
    if (Util.isAssignExpr(expr)) {
      fAssign = false;
      expr.right.accept(this, o); 
      fAssign = true;
      expr.left.accept(this, o);
      return null;
    }
    else {
      return visitExpr(expr, o);
    }
  }

  @Override
  public Object visitUnaryExpr(final /*@non_null*/ UnaryExpr x, final Object o) {
    fAssign = true;
    return visitExpr(x, o);
  }

  
  public static Set<Type> getVisibleTypeSet(final RoutineDecl x) {
    final VisibleTypeCollector vtc = new VisibleTypeCollector();
    x.accept(vtc, null);
    return vtc.fTypeSet;
  }
  public static Set<org.apache.bcel.generic.Type> getBCELVisibleTypeSet(final RoutineDecl x) {
    final Set<Type> s = getVisibleTypeSet(x);
    final Set<org.apache.bcel.generic.Type> ret = 
      new HashSet<org.apache.bcel.generic.Type>();
    for (Type t: s) {
      if (t instanceof TypeSig) {
        JavaClass jc = mobius.directVCGen.formula.Translator.getInst().translate((TypeSig)t);
        
        ret.add(new ObjectType(jc.getClassName()));
      }
    }
    return ret;
  }

}
