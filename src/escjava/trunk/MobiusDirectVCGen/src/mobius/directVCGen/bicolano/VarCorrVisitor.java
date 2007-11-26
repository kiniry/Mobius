package mobius.directVCGen.bicolano;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafe.ast.ASTNode;
import javafe.ast.FormalParaDecl;
import javafe.ast.RoutineDecl;
import javafe.ast.VarDeclStmt;
import javafe.ast.Visitor;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Ref;

import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;

/**
 * This class is used mainly to decorate an ESC/Java method with
 * informations about its variable, using the final format.
 * It fills a {@link VarCorrDecoration} structure and adds it to the method.
 * 
 * @see mobius.directVCGen.bicolano.VarCorrDecoration
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class VarCorrVisitor extends Visitor {
  
  /** the variables and their bytecode correspondence. */
  private final Map<QuantVariableRef, LocalVariableGen> fVariables = 
    new HashMap<QuantVariableRef, LocalVariableGen>();
  /** the currently treated method. */
  private final MethodGen fMet;
  
  /** the variable that could be 'made old'. */
  private final List<QuantVariableRef> fOld = new ArrayList<QuantVariableRef>();
  
  
  /**
   * The constructor.
   * @param decl the ESC/Java representation of the method
   * @param met the bcel representation of the method
   */
  private VarCorrVisitor(final RoutineDecl decl, 
                            final MethodGen met) {
    final LocalVariableGen[] tab = met.getLocalVariables();
    fMet = met;
    if (tab.length == 0) {
      return;
    }
    fOld.add(Ref.varThis);
    int i = 1;
    for (FormalParaDecl para: decl.args.toArray()) {
      final QuantVariableRef qvr = Expression.rvar(para);
      
      fOld.add(qvr); 
      i++;
    }
  }

  /**
   * Adds the variable which is being declared to the list of variables.
   * @param x the variable being declared
   */
  @Override
  public /*@non_null*/ void visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x) { 
    final LocalVariableGen[] tab = fMet.getLocalVariables();
    for (LocalVariableGen var : tab) {
      if (var.getName().equals(x.decl.id.toString())) {
        fVariables.put(Expression.rvar(x.decl), var);
      }
    }
    
  }

  /**
   * Returns all the variables necessary for a method, and
   * annotates the escjava method with all some informations about
   * the variable. Basically it decorates the method with a fully filled
   * {@link VarCorrDecoration} structure. 
   * @param decl the ESC/Java declaration of the method
   * @param met the bcel version of the method
   * @return a list of variables.
   */
  public static List<QuantVariableRef> getVariables(final RoutineDecl decl, 
                                    final MethodGen met) {
    final VarCorrVisitor vis = new VarCorrVisitor(decl, met);
    decl.accept(vis);
    
    VarCorrDecoration.inst.set(decl, vis.fVariables, vis.fOld);
 
    return VarCorrDecoration.inst.get(decl);
  }

  /**
   * Just goes recursively through all the children nodes :).
   * @param x the currently inspected node
   */
  @Override
  public void visitASTNode(final ASTNode x) {
    final int max = x.childCount();
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        ((ASTNode) child).accept(this);
      }
    }
  }
}
