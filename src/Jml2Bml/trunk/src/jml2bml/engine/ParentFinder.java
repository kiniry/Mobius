package jml2bml.engine;

import java.util.HashMap;
import java.util.Map;

import com.sun.source.tree.Tree;

import experiments.ExtendedJmlTreeScanner;

public class ParentFinder extends ExtendedJmlTreeScanner<Tree, Tree> {
  private Map<Tree, Tree> parents;

  public ParentFinder() {
    parents = new HashMap<Tree, Tree>();
  }

  public Map<Tree, Tree> getParents() {
    return parents;
  }

  @Override
  protected Tree preVisit(Tree node, Tree p) {
    parents.put(node, p);
    return node;
  }
}
