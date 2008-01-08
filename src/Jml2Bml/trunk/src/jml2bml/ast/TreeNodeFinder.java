/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.ast;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import com.sun.source.tree.BlockTree;
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

    public Tree visitBlock(BlockTree block, Tree p){
      Tree result = super.visitBlock(block, p);
      Iterator<? extends StatementTree> iter = block.getStatements().iterator();
      if (iter.hasNext()){
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

  /**
   * Map of parents of tree nodes.
   */
  private Map<Tree, Tree> parents;

  /**
   * Maps a statemet to the next statement in a block.
   */
  private Map<StatementTree, StatementTree> nextStatemtentMap;

  public TreeNodeFinder(final Tree tree) {
    parents = new HashMap<Tree, Tree>();
    nextStatemtentMap = new HashMap<StatementTree, StatementTree>();
    tree.accept(new ParentFinder(), null);
  }

  /**
   * Finds ancestor of treeElement in current tree.
   *
   * @param treeElement the element to find ancestor of
   * @param ancestorKind the kind of ancestor to find
   * @return the ancestor of treeElement that is of kind ancestorKind
   */
  public Tree getAncestor(Tree treeElement, final Kind ancestorKind) {
    if (!parents.containsKey(treeElement))
      throw new RuntimeException("tree element not from current tree");

    treeElement = parents.get(treeElement);
    while (treeElement != null) {
      if (treeElement.getKind() == ancestorKind)
        return treeElement;
      treeElement = parents.get(treeElement);
    }
    return null;
  }

  public StatementTree getNextStatement(final StatementTree statement) {
    return nextStatemtentMap.get(statement);
  }
}
