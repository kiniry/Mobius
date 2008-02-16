/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-28 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.bytecode.LoopDescription;
import jml2bml.bytecode.LoopDetector;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.InstructionHandle;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;

import annot.attributes.SingleLoopSpecification;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;

import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.LineMap;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0.0-1
 */
public class LoopInvariantRule extends TranslationRule<String, Symbols> {
  /**
   * Application context.
   */
  private final Context myContext;

  /**
   * Collection of loops.
   */
  private Collection<SourceLoopDescription> loops;

  /**
   * Helps to find ancestors for given nodes.
   */
  private TreeNodeFinder finder;

  //  private class LoopProcessor extends TranslationRule<String, Symbols> {
  //    protected String preVisit(Tree node, Symbols symb) {
  //      throw new NotTranslatedException("Not implemented: " + node);
  //    }
  //
  //    public String visitJmlForLoop(JmlForLoop node, Symbols symb) {
  //      long line = BytecodeUtil.getLineNumber(node, myContext.get(LineMap.class));
  //      return "";
  //    }
  //  }

  /**
   * Creates new instance of the LoopInvariantRule.
   * @param context application context
   */
  public LoopInvariantRule(final Context context) {
    super();
    this.myContext = context;
  }

  private class SourceLoopDescription {
    private LoopDescription loopDesc;

    private int sourceBegin;

    private int sourceEnd;

    public SourceLoopDescription(LoopDescription loopDesc, int line) {
      this.loopDesc = loopDesc;
      this.sourceBegin = this.sourceEnd = line;
    }

    public void updateEnds(int line) {
      if (line < sourceBegin)
        sourceBegin = line;
      if (line > sourceEnd)
        sourceEnd = line;
    }
  }

  public String visitJmlMethodDecl(JmlMethodDecl node, Symbols symb) {
    final BCClass clazz = symb.findClass();
    final BCMethod bcMethod = BytecodeUtil.findMethod(node.getName(), clazz);
    finder = myContext.get(TreeNodeFinder.class);

    final List<LoopDescription> bytecodeLoops =
      LoopDetector.detectLoop(bcMethod);
    final Map<InstructionHandle, Integer> lineNumbers =
      BytecodeUtil.getLineNumberMap(bcMethod);
    final Map<LoopDescription, SourceLoopDescription> sourceLoops =
      new HashMap<LoopDescription, SourceLoopDescription>();

    int sourceLine = -1;
    for (InstructionHandle ih : bcMethod.getBcelMethod().getInstructionList()
        .getInstructionHandles()) {
      if (lineNumbers.containsKey(ih))
        sourceLine = lineNumbers.get(ih);
      for (LoopDescription loop : bytecodeLoops)
        if (loop.getLoopStartHandle().getPosition() <= ih.getPosition() &&
            loop.getLoopEndHandle().getPosition() >= ih.getPosition()) {
          if (sourceLoops.containsKey(loop))
            sourceLoops.get(loop).updateEnds(sourceLine);
          else
            sourceLoops.put(loop, new SourceLoopDescription(loop, sourceLine));
        }
    }
    loops = sourceLoops.values();

    return super.preVisit(node, symb);
  }

  public String visitJmlStatementLoop(final JmlStatementLoop node,
                                      final Symbols symb) {
    final BCClass clazz = symb.findClass();

    //Find an enclosing method
    final MethodTree method = (MethodTree) finder.getAncestor(node,
                                                              Kind.METHOD);

    final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), clazz);

    //loop pos
    Map<JCTree, Integer> endPosTable = myContext.get(JCCompilationUnit.class).endPositions;

    Tree loopNode = (JCTree) finder.getParent(node);
    if (loopNode instanceof LabeledStatementTree)
      //FIXME: workaround for parser bug
      loopNode = finder.getNextSibling(loopNode);

    final LineMap lineMap = myContext.get(LineMap.class);

    final long beginLine =
      lineMap.getLineNumber(((JCTree) loopNode).getStartPosition());
    final long endLine =
      lineMap.getLineNumber(((JCTree) loopNode).getEndPosition(endPosTable));

    SourceLoopDescription matchedLoop = null;

    for (SourceLoopDescription loopDesc : loops)
      if (loopDesc.sourceBegin >= beginLine && loopDesc.sourceEnd <= endLine) {
        if (matchedLoop == null)
          matchedLoop = loopDesc;
        else if (matchedLoop.sourceBegin >= loopDesc.sourceBegin &&
            matchedLoop.sourceEnd <= loopDesc.sourceEnd)
          matchedLoop = loopDesc;
        else if (matchedLoop.sourceBegin <= loopDesc.sourceBegin &&
            matchedLoop.sourceEnd >= loopDesc.sourceEnd)
          continue;
        else
          throw new NotTranslatedException("Wrong loops in bytecode??");
      }

    if (matchedLoop == null)
      throw new NotTranslatedException("No matching loop found");

    final AbstractFormula invariantFormula =
      TranslationUtil.getFormula(node.expression, symb, myContext);

    //FIXME: there can be many exactly equal loops
    for (SourceLoopDescription loop : loops)
      if (loop.sourceBegin == matchedLoop.sourceBegin &&
          loop.sourceEnd == matchedLoop.sourceEnd) {
        final InstructionHandle loopAdd =
          loop.loopDesc.getInstructionToAnnotate().getInstruction();

        final int count = bcMethod.getAmap().getAllAt(loopAdd).size();
        final SingleLoopSpecification loopSpecs =
          new SingleLoopSpecification(bcMethod, loopAdd, count, null,
                                      invariantFormula, null);
        bcMethod.addAttribute(loopSpecs);
      }

    return "";
  }

  //  private class LineNumberFinder extends ExtendedJmlTreeScanner<Void, Void> {
  //    public int lowest = Integer.MAX_VALUE;
  //    public int highest = Integer.MIN_VALUE;
  //    private Map<JCTree, Integer> endPosTable;
  //    
  //    public LineNumberFinder() {
  //      endPosTable = myContext.get(JCCompilationUnit.class).endPositions;
  //    }
  //    
  //    private void updateLowest(int value) {
  //      if (value<lowest)
  //        lowest = value;
  //    }
  //    
  //    private void updateHighest(int value) {
  //      if (value>highest)
  //        highest = value;
  //    }
  //    
  //    protected Void preVisit(final Tree node, final Void p) {
  //      JmlParser parser = myContext.get(JmlParser.class);
  //      if (! finder.isInJmlComment(node)) {
  //        //TODO: here also only translated to bytecode nodes should be used
  //        int pos = ((JCTree)node).getStartPosition();
  //        int endPos = ((JCTree)node).getEndPosition(endPosTable);
  //        if (pos>0) {
  //          if (node instanceof BlockTree) {
  //          } else if (node instanceof JmlDoWhileLoop) {
  //            JmlDoWhileLoop doWhileNode = (JmlDoWhileLoop) node;
  //            //FIXME: this is wrong!!
  //            updateLowest(endPos);
  //            updateHighest(pos);
  //          } else {
  //            updateLowest(pos);
  //            updateHighest(pos);
  //          }
  //        }
  //      }
  //      return super.preVisit(node, p);
  //    }
  //  }

  //  private int findLowestLineNumber(final Tree stmt) {
  ////    int pos = ((JCTree)node).getStartPosition();
  //    final LineNumberFinder visitor = new LineNumberFinder();
  //    stmt.accept(visitor, null);
  //    return visitor.lowest;
  //  }
  //  
  //  public InstructionHandle getInstructionAtPos(int pos, final BCMethod method) {
  //    final LineMap lineMap = myContext.get(LineMap.class);
  //    final long sourceLine = lineMap.getLineNumber(pos);
  //    for (LineNumberGen lng : method.getBcelMethod().getLineNumbers()) {
  //      if (sourceLine == lng.getSourceLine())
  //        return lng.getInstruction();
  //    }
  //    return null;
  //  }

  //  public InstructionHandle translateStatement(final Tree stmt,
  //                                              final BCMethod method) {
  //    if (stmt == null) {
  //      return method.getInstructions().getEnd();
  //    } else {
  //      final LineMap lineMap = myContext.get(LineMap.class);
  //      int lowestLineNum = findLowestLineNumber(stmt);
  //      final long sourceLine = lineMap.getLineNumber(520);
  //      for (LineNumberGen lng : method.getBcelMethod().getLineNumbers()) {
  //        //FIXME: can one source line have more than one line number in output??
  //        if (sourceLine == lng.getSourceLine())
  //          return lng.getInstruction();
  //      }
  //    }
  //    throw new NotTranslatedException("Error with finding target instruction in bytecode");
  //  }
}
