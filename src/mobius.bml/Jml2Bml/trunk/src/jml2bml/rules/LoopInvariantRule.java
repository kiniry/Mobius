/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-28 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
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
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.InstructionHandle;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;

import annot.attributes.method.InCodeAnnotation;
import annot.attributes.method.SingleList;
import annot.attributes.method.SingleLoopSpecification;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.formula.Predicate0Ar;

import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.LineMap;
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
public class LoopInvariantRule extends TranslationRule < String, Symbols > {

  /**
   * Class for updating symbol table - we need to add loop condition to symbols.
   * @author kjk (kjk@mimuw.edu.pl)
   * @version 0.0-1
   */
  private class SymbolTableUpdater extends TranslationRule < Symbols,
                                                             Symbols > {
    /** A SymbolsBuilder field. */
    private SymbolsBuilder builder;

    /** Default constructor. */
    public SymbolTableUpdater() {
      this.builder = new SymbolsBuilder(myContext);
    }

    /**
     * Default preVisit method. Throws NotTranslatedRuntimeException.
     * @param node visited node
     * @param symb symbol table
     * @return never reached.
     */
    @Override
    protected Symbols preVisit(final Tree node, final Symbols symb) {
      throw new NotTranslatedRuntimeException("Not implemented: " +
                                              node.getClass() + " " + node);
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
      Symbols newSymbols = new Symbols(p);
      for (JCStatement stmtNode : node.init)
        newSymbols = stmtNode.accept(builder, newSymbols);
      for (JCStatement stmtNode : node.step)
        newSymbols = stmtNode.accept(builder, newSymbols);
      if (node.cond != null)
        newSymbols = node.cond.accept(builder, newSymbols);
      return newSymbols;
    }

    /**
     * Updates symbol table for 'while' loop.
     *
     * @param node visited node
     * @param p symbol table
     * @return updated symbol table
     */
    @Override
    public Symbols visitJmlWhileLoop(final JmlWhileLoop node, final Symbols p) {
      return node.cond.accept(builder, new Symbols(p));
    }

    /**
     * Updates symbol table for 'do-while' loop.
     *
     * @param node visited node
     * @param p symbol table
     * @return updated symbol table
     */
    @Override
    public Symbols visitJmlDoWhileLoop(final JmlDoWhileLoop node,
                                       final Symbols p) {
      return node.cond.accept(builder, new Symbols(p));
    }

    /**
     * Updates symbol table for enhanced 'for' loop.
     *
     * @param node visited node
     * @param p symbol table
     * @return updated symbol table
     */
    @Override
    public Symbols visitJmlEnhancedForLoop(final JmlEnhancedForLoop node,
                                           final Symbols p) {
      return node.var.accept(builder, new Symbols(p));
    }
  }

  /** Application context. */
  private final Context myContext;

  /** Loops found in bytecode of the current method. */
  private Collection < SourceLoopDescription > loops;

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
     * @param aloopDesc bytecode loop description.
     * @param line line to use in the beginning as start and end position of
     * loop in source code.
     */
    public SourceLoopDescription(final LoopDescription aloopDesc,
                                 final int line) {
      this.loopDesc = aloopDesc;
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
    final BCMethod bcMethod = BytecodeUtil.findMethod(node, clazz);
    finder = myContext.get(TreeNodeFinder.class);

    if (bcMethod.getBcelMethod().isAbstract())
      return null;
    final List < LoopDescription > bytecodeLoops = LoopDetector
        .detectLoop(bcMethod);
    final Map < InstructionHandle, Integer > lineNumbers = BytecodeUtil
        .getLineNumberMap(bcMethod);
    final Map < LoopDescription, SourceLoopDescription > sourceLoops =
      new HashMap < LoopDescription, SourceLoopDescription >();

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
    for (SourceLoopDescription loopDesc : loops){
      System.err.println(loopDesc.sourceBegin + " " + loopDesc.sourceEnd + "   " + beginLine + endLine);
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
          throw new NotTranslatedRuntimeException("Wrong loops in bytecode??");
      }
    }
    if (matchedLoop == null)
      throw new NotTranslatedRuntimeException("No matching loop found");
    return matchedLoop;
  }

  /**
   * Inserts loop specifications to correct instructions in bytecode.
   * @param loopNode loop node which has specification
   * @param symb symbol table
   * @param modifies modify list to insert
   * @param invariant loop invariant to insert
   * @param decreases decreases to insert
   */
  private void insertSpecs(final Tree loopNode, final Symbols symb,
                           final BCExpression invariant,
                           final BCExpression decreases) {
    final BCClass clazz = symb.findClass();
    final JmlMethodDecl method = (JmlMethodDecl) finder.getAncestor(loopNode,
                                                              Kind.METHOD);
    final Map < JCTree, Integer > endPosTable = myContext
        .get(JCCompilationUnit.class).endPositions;

    final LineMap lineMap = myContext.get(LineMap.class);
    final long beginLine = lineMap.getLineNumber(((JCTree) loopNode)
        .getStartPosition());
    final long endLine = lineMap.getLineNumber(((JCTree) loopNode)
        .getEndPosition(endPosTable));

    final SourceLoopDescription matchedLoop = findMatchedLoop(beginLine,
                                                              endLine);

    //FIXME: there can be many exactly equal loops
    for (SourceLoopDescription loop : loops)
      if (loop.sourceBegin == matchedLoop.sourceBegin &&
          loop.sourceEnd == matchedLoop.sourceEnd) {
        final InstructionHandle loopAdd = loop.loopDesc
            .getInstructionToAnnotate().getInstruction();
        addLoopSpecs(BytecodeUtil.findMethod(method, clazz), loopAdd,
                     invariant, decreases);
      }
  }

  /**
   * Checks if invariant is an empty one.
   * @param expr invariant expression to check
   * @return if expr is empty or not
   */
  private boolean isEmptyInvariant(final BCExpression expr) {
    return (expr instanceof Predicate0Ar);
  }

  /**
   * Checks if decreases is an empty one.
   * @param expr decreases expression to check
   * @return if expr is empty or not
   */
  private boolean isEmptyDecreases(final BCExpression expr) {
    return (expr instanceof NumberLiteral);
  }

  /**
   * Adds loops specification to instruction handle of specific method. Gets
   * last inserted SingleLoopSpecification and checks if new modifiers,
   * invariant or decreases collide (existed ands needs to be added) with
   * previous one. If not - it updates the specification attribute. Otherwise
   * it adds a new one.
   * @param bcMethod method where attribute should be added
   * @param ih the instruction handle to add attribute to
   * @param invariant invariant of the attribute
   * @param decreases decreases of the attribute
   */
  private void addLoopSpecs(final BCMethod bcMethod,
                            final InstructionHandle ih,
                            final BCExpression invariant,
                            final BCExpression decreases) {
    final SingleList ihs = bcMethod.getAmap().getAllAt(ih);
    SingleLoopSpecification specs = null;
    //Find last SingleLoopSpecification annotation in this place
    for (int i = ihs.size() - 1; i >= 0; i--) {
      final InCodeAnnotation annot = ihs.get(i);
      if (annot instanceof SingleLoopSpecification) {
        specs = (SingleLoopSpecification) annot;
        break;
      }
    }
    BCExpression oldInvariant = null;
    BCExpression oldDecreases = null;

    boolean addNew = false;
    if (specs == null)
      addNew = true;
    else {
      final ExpressionRoot[] allExprs = specs.getAllExpressions();
      oldInvariant = allExprs[SingleLoopSpecification.INVARIANT_POS].getSubExpr(0);
      if (invariant != null) {
        if (!isEmptyInvariant(oldInvariant))
          addNew = true;
        else
          oldInvariant = invariant;
      }
      oldDecreases = allExprs[SingleLoopSpecification.VARIANT_POS].getSubExpr(0);
      if (decreases != null) {
        if (!isEmptyDecreases(oldDecreases))
          addNew = true;
        else
          oldDecreases = decreases;
      }
    }
    final int count = addNew ? ihs.size() : specs.getMinor();
    final SingleLoopSpecification attr = addNew ?
        new SingleLoopSpecification(bcMethod, ih, count, invariant,
                                    decreases) :
        new SingleLoopSpecification(bcMethod, ih, count,
                                      oldInvariant, oldDecreases);
    if (addNew)
      bcMethod.addAttribute(attr);
    else
      bcMethod.getAmap().replaceAttribute(specs, attr);
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
    Tree loopNode = (JCTree) finder.getParent(node);
    if (loopNode instanceof LabeledStatementTree)
      //FIXME: workaround for parser bug
      loopNode = finder.getNextSibling(loopNode);
    final Symbols newSymbols = loopNode.accept(new SymbolTableUpdater(), symb);

    BCExpression invariant = null;
    BCExpression decreases = null;
    if (node.token == JmlToken.LOOP_INVARIANT)
      invariant = node.expression.accept(RulesFactory.getExpressionRule(myContext), newSymbols);
//      invariant = TranslationUtil.getFormula(node.expression, newSymbols,
//                                             myContext);
    else if (node.token == JmlToken.DECREASES)
      decreases = node.expression.accept(RulesFactory
          .getExpressionRule(myContext), newSymbols);
    else
      throw new NotTranslatedRuntimeException(
         "Not translating JmlStatementLoop of " + "type: " + node.token);
    insertSpecs(loopNode, newSymbols, invariant, decreases);
    return "";
  }
}