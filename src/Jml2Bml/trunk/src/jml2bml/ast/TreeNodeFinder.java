/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.ast;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;

import com.sun.source.tree.BlockTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;

/**
 * An utility class responsible for finding ancestors of nodes in a tree.
 *
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @author kjk    (kjk@mimuw.edu.pl)
 */
public class TreeNodeFinder {
  /**
   * Class responsible for filling {@code parents} field in
   * {@code AncestorFinder} class.
   *
   * @author Jedrek (fulara@mimuw.edu.pl)
   * @author kjk    (kjk@mimuw.edu.pl)
   *
   */
  private class ParentFinder extends ExtendedJmlTreeScanner<Tree, Tree> {

    @Override
    protected Tree preVisit(Tree node, Tree p) {
      parents.put(node, p);
      return node;
    }

    public Tree visitJmlClassDecl(JmlClassDecl classNode, Tree node) {
      final Tree result = super.visitClass(classNode, node);
      final Iterator<? extends Tree> iter = classNode.getMembers().iterator();
      if (iter.hasNext()) {
        Tree stmt = iter.next();
        while (iter.hasNext()) {
          final Tree next = iter.next();
          nextSiblingMap.put(stmt, next);
          stmt = next;
        }
        nextSiblingMap.put(stmt, null);
      }
      return result;
    }

    public Tree visitBlock(BlockTree block, Tree p) {
      final Tree result = super.visitBlock(block, p);
      final Iterator<? extends StatementTree> iter = block.getStatements()
          .iterator();
      if (iter.hasNext()) {
        StatementTree stmt = iter.next();
        while (iter.hasNext()) {
          final StatementTree next = iter.next();
          nextStatemtentMap.put(stmt, next);
          stmt = next;
        }
        nextStatemtentMap.put(stmt, null);
      }
      return result;
    }
  }

  /** Map of parents of tree nodes. */
  private Map<Tree, Tree> parents;

  /** Maps a statement to the next statement in a block. */
  private Map<StatementTree, StatementTree> nextStatemtentMap;

  /** Maps a tree node to next sibling in a tree. */
  private Map<Tree, Tree> nextSiblingMap;

  public TreeNodeFinder(final Tree tree) {
    parents = new HashMap<Tree, Tree>();
    nextStatemtentMap = new HashMap<StatementTree, StatementTree>();
    nextSiblingMap = new HashMap<Tree, Tree>();
    tree.accept(new ParentFinder(), null);
  }

  /**
   * Finds ancestor of treeElement in current tree.
   *
   * @param treeElement the element to find ancestor of
   * @param ancestorKind the kind of ancestor to find
   * @return the ancestor of treeElement that is of kind ancestorKind,
   *         when no ancestor of that kind found {@code null} is a result.
   */
  public Tree getAncestor(final Tree treeElement, final Kind ancestorKind) {
    if (!parents.containsKey(treeElement))
      throw new RuntimeException("tree element not from current tree");

    Tree element = parents.get(treeElement);
    while (element != null) {
      if (element.getKind() == ancestorKind)
        return element;
      element = parents.get(element);
    }
    return null;
  }

  /**
   * Finding ancestor of element that is of desired type
   *
   *
   * @param treeElement element to find ancestor of
   * @param ofClass the class we want to find
   * @return the ancestor of treeElement that is assignable to type ofClass
   */
  //TODO: Is this dirty, should be changed?? (we can't locate JML nodes differently now)
  public Tree getAncestor(final Tree treeElement, final Class<?> ofClass) {
    if (!parents.containsKey(treeElement))
      throw new RuntimeException("tree element not from current tree");

    Tree element = parents.get(treeElement);
    while (element != null) {
      if (ofClass.isAssignableFrom(element.getClass()))
        return element;
      element = parents.get(element);
    }
    return null;
  }

  /**
   * Method finds a statement following {@code statement}.
   *
   * @param statement
   * @return a statement following statement in parameter
   *         when no statement after {@code null} is a result.
   */
  public StatementTree getNextStatement(final StatementTree statement) {
    return nextStatemtentMap.get(statement);
  }

  public Tree getNextMember(final Tree classMember) {
    return nextSiblingMap.get(classMember);
  }
}
