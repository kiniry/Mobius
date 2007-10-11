package mobius.directVCGen.formula;

import java.util.List;
import java.util.Vector;

import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.vcgen.DirectVCGen;

import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.Term;

import javafe.ast.RoutineDecl;



public class Util {
  
  /**
   * 
   * @param decl
   * @return The name of the Annotations version of the method
   */
  public static String getMethodName(RoutineDecl decl) {
    return decl.parent.id + "Annotations." + decl.id();
  }
  
  public static InstructionHandle findLastInstruction(List<LineNumberGen> list) {
    final InstructionHandle baseih = list.get(0).getInstruction();
    InstructionHandle ih = baseih.getNext();
    // first we find the first goto
    while (!(ih.getInstruction() instanceof GotoInstruction)) {
      ih = ih.getNext();
    }
    final GotoInstruction bi =  (GotoInstruction) ih.getInstruction();
    return bi.getTarget();
  }
  
  public static boolean belongs(LocalVariableGen local, List<LineNumberGen> lines) {
    
    for (LineNumberGen line: lines) {
      final int linePc = line.getLineNumber().getStartPC();
      final int localPc = local.getStart().getPosition();
      if ((linePc >= localPc) &&
          (line.getLineNumber().getStartPC() <= localPc + local.getStart().getPosition())) {
        return true;
      }
    }
    return false;
  }
  public static LineNumberGen getLineNumberFromLine(MethodGen met, int lineNum) {
    final LineNumberGen [] tab = met.getLineNumbers();
    if (tab.length == 0) {
      return null;
    }
    LineNumberGen min = tab[0];
    int oldspan = Math.abs(min.getSourceLine() - lineNum);
    
    for (LineNumberGen line: tab) {
      final int span = (Math.abs(line.getSourceLine() - lineNum));
      if (span  > 0) {
        if (span < oldspan) {
          min = line;
          oldspan = span;
        }
      }
    }
    return min;
  }
  public static List<LineNumberGen> getLineNumbers(MethodGen met, int lineNum) {
    final List<LineNumberGen> res = new Vector<LineNumberGen>();
    final LineNumberGen first = Util.getLineNumberFromLine(met, lineNum);
    final LineNumberGen [] tab = met.getLineNumbers();
    
    for (LineNumberGen line: tab) {
      if (line.getLineNumber().getLineNumber() == first.getLineNumber().getLineNumber()) {
        res.add(line);
      }
    }
    return res;
  }
  
  /**
   * @deprecated
   * @param lines
   * @return
   */
  public static List<LocalVariableGen> getValidVariables(MethodGen met, List<LineNumberGen> lines) {
    final List<LocalVariableGen> res = new Vector<LocalVariableGen>();
    final LocalVariableGen[] lvt = met.getLocalVariables();
    int skip = met.getArgumentNames().length; // we skip the n first variables
   
    for (LocalVariableGen local: lvt) {
      if (skip > 0) {
        skip--;
      }
      else if (Util.belongs(local, lines)) {
        
        res.add(local);
      }
    }
    return res;
  }
  
  public static Term getAssertion(RoutineDecl meth, 
                                  AAnnotation annot) {
    final Term res;
    if (DirectVCGen.fByteCodeTrick) {
      final String methname = Util.getMethodName(meth);
      final Term[] tab = annot.fArgs.toArray(new Term [annot.fArgs.size()]);
      res = Expression.sym(methname + ".mk_" + annot.fName, tab);
    }
    else {
      res = annot.formula;
    }
    return res;
  }
}
