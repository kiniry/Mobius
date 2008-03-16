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

import jml2bml.ast.SymbolsBuilder;
import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.bytecode.LoopDescription;
import jml2bml.bytecode.LoopDetector;
import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.InstructionHandle;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
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
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

/**
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0.0-1
 */
public class LoopInvariantRule extends TranslationRule<String, Symbols> {

  /**
   * Class for updating symbol table - we need to add loop condition to symbols.
   * @author kjk (kjk@mimuw.edu.pl)
   * @version 0.0-1
   */
  private class SymbolTableUpdater extends TranslationRule<Symbols, Symbols> {
    /**
     * Default preVisit method. Throws NotTranslatedException.
     * @param node visited node
     * @param symb symbol table
     * @return never reached.
     */
    @Override
    protected Symbols preVisit(final Tree node, final Symbols symb) {
      throw new NotTranslatedException("Not implemented: " + node.getClass() +
                                       " " + node);
    }

    /**
     * Updates symbol table for 'for' loop.
     *
     * @param node visited node
     * @param p symbol table
     * @return updated symbol table
     */
    @Override
    public Symbols visitJmlForLoop(final JmlForLoop node, final Symbols p) {
      final SymbolsBuilder builder = new SymbolsBuilder(myContext);
      Symbols newSymbols = new Symbols(p);
      for (JCStatement stmtNode : node.init)
        newSymbols = stmtNode.accept(builder, newSymbols);
      for (JCStatement stmtNode : node.step)
        newSymbols = stmtNode.accept(builder, newSymbols);
      newSymbols = node.cond.accept(builder, newSymbols);
      return newSymbols;
    }
  }
  /** Application context. */
  private final Context myContext;

  /** Loops found in bytecode of the current method. */
  private Collection<SourceLoopDescription> loops;

  /** Helps to find ancestors for given nodes. */
  private TreeNodeFinder finder;

  /**
   * Creates new instance of the LoopInvariantRule.
   * @param context application context
   */
  public LoopInvariantRule(final Context context) {
    super();
    this.myContext = context;
  }

  /**
   * A class representing destription of loop joining source code with bytecode.
   * Containst loop start position, loop end position and a bytecode loop
   * description.
   *
   * @author kjk (kjk@mimuw.edu.pl)
   */
  private class SourceLoopDescription {
    /** The bytecode loop description. */
    private LoopDescription loopDesc;

    /** A begin line of the loop in source code. */
    private int sourceBegin;

    /** An end line of the loop in source code. */
    private int sourceEnd;

    /**
     * Constructor of the class.
     * @param loopDesc bytecode loop description.
     * @param line line to use in the beginning as start and end position of
     * loop in source code.
     */
    public SourceLoopDescription(final LoopDescription loopDesc,
                                 final int line) {
      this.loopDesc = loopDesc;
      this.sourceBegin = line;
      this.sourceEnd = line;
    }

    /**
     * Updates ends of the loop given new line number.
     * @param line a line that contains the loop
     */
    public void updateEnds(final int line) {
      if (line < sourceBegin)
        sourceBegin = line;
      if (line > sourceEnd)
        sourceEnd = line;
    }
  }

  /**
   * Preparing of the translation. All loops of the method are found in
   * bytecode and translated to source loop descriptions according to method
   * line table.
   * @param node method node
   * @param symb current symbol table
   * @return null
   */
  @Override
  public String visitJmlMethodDecl(final JmlMethodDecl node,
                                   final Symbols symb) {
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

  /**
   * Finds a best loop in bytecode ({@code loops}) to loop in source between
   * lines ({@code beginLine}, {@code endLine}).
   *
   * @param beginLine beginning of the source loop
   * @param endLine ending of the source loop
   * @return matched loop in bytecode
   */
  private SourceLoopDescription findMatchedLoop(final long beginLine,
                                                final long endLine) {
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
    return matchedLoop;
  }

  /**
   * Translation of loop statement.
   * @param node statement loop node to translate.
   * @param symb current symbol table.
   * @return empty string
   */
  @Override
  public String visitJmlStatementLoop(final JmlStatementLoop node,
                                      final Symbols symb) {
    final BCClass clazz = symb.findClass();
    final MethodTree method = (MethodTree) finder.getAncestor(node,
                                                              Kind.METHOD);
    final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), clazz);
    final Map<JCTree, Integer> endPosTable =
      myContext.get(JCCompilationUnit.class).endPositions;
    Tree loopNode = (JCTree) finder.getParent(node);
    if (loopNode instanceof LabeledStatementTree)
      //FIXME: workaround for parser bug
      loopNode = finder.getNextSibling(loopNode);
    final LineMap lineMap = myContext.get(LineMap.class);

    final long beginLine =
      lineMap.getLineNumber(((JCTree) loopNode).getStartPosition());
    final long endLine =
      lineMap.getLineNumber(((JCTree) loopNode).getEndPosition(endPosTable));

    final SourceLoopDescription matchedLoop = findMatchedLoop(beginLine,
                                                              endLine);
    final Symbols newSymbols = loopNode.accept(new SymbolTableUpdater(), symb);
    final AbstractFormula invariantFormula =
      TranslationUtil.getFormula(node.expression, newSymbols, myContext);

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
}
