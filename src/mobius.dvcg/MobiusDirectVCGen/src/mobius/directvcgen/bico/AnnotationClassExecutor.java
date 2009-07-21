package mobius.directvcgen.bico;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.List;

import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.executors.ClassExecutor;
import mobius.directvcgen.formula.Expression;
import mobius.directvcgen.formula.Formula;
import mobius.directvcgen.formula.Heap;
import mobius.directvcgen.formula.Logic;
import mobius.directvcgen.formula.Lookup;
import mobius.directvcgen.formula.Ref;
import mobius.directvcgen.formula.Translator;
import mobius.directvcgen.formula.Type;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;


/**
 * Write the normal class definitions like a normal executor,
 * plus a file for the annotations.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AnnotationClassExecutor extends ClassExecutor {
  /** the current class which is inspected. */
  private ClassGen fClass;
  

  
  /**
   * Create an executor that can produce annotations.
   * @param be the parent executor.
   * @param cg the class which is currently treated
   * @param gen the generator used to annotate the AST with first order
   * logic formulas
   * @throws FileNotFoundException in case the file cannot be written on the disk
   */
  public AnnotationClassExecutor(final AnnotationExecutor be, 
                                 final ClassGen cg, 
                                 final IAnnotationGenerator gen) throws FileNotFoundException {
    super(be, cg);
    fClass = cg;
    if (!gen.annotateClass(getRepository(), fClass)) {
    	throw new IllegalArgumentException("Generator failed.");
    }
  }
  
 
  
  /**
   * Do the annotation definition for each class.
   */
  @Override
  public void doClassDefinition() {
    super.doClassDefinition();
    

    try {
      final Method[] methods = fClass.getMethods(); 
      
      final CoqStream anOut = new CoqStream(new FileOutputStream(
                                         new File(getWorkingDir(), 
                                                  getModuleName() + "_annotations.v")));
    
      anOut.println(getLibPath());
      
      anOut.println("Require Export defs_types.");
      anOut.println("Require Export Bool.");
      anOut.println("Require Export Sumbool.");
      anOut.println("Require Export ImplemSWp.");
      

      anOut.println("Import Mwp.");

      anOut.incPrintln("Module " + this.getModuleName() + "Annotations.");
      
      for (Method met: methods) {
        final AnnotationMethodExecutor ame = 
            new AnnotationMethodExecutor(this, anOut, fClass, met);
        ame.start();
      }
      doInvariant(anOut);
      anOut.decPrintln("End " + this.getModuleName() + "Annotations.\n");  
    } 
    
    catch (FileNotFoundException e) {
      e.printStackTrace();
    }
  }



  private void doInvariant(CoqStream out) {
    final Term term = Lookup.getInst().getInvariant(fClass.getJavaClass());
    QuantVariableRef h = Heap.var;
    QuantVariableRef t = Type.translateToType(
                       new ObjectType(fClass.getJavaClass().getClassName()));
    QuantVariableRef self = Ref.varThis;
    List<QuantVariableRef> l = new ArrayList<QuantVariableRef>();
    l.add(h); l.add(self); 
    Term f = Logic.forall(l, Logic.fullImplies(Logic.inv(h, self, t), term));
    
    out.println("Variable invariant :");
    out.incPrintln();
    out.println(Formula.generateFormulas(f) + ".");
    out.decTab();
    out.println();
  }




}
