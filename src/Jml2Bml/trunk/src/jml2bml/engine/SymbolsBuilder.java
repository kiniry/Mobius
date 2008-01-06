package jml2bml.engine;

import jml2bml.ast.ExtendedJmlTreeScanner;

import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.source.tree.VariableTree;

public class SymbolsBuilder extends ExtendedJmlTreeScanner<Symbols, Symbols>{

  @Override
  public Symbols visitJmlVariableDecl(JmlVariableDecl node, Symbols p) {
    
    System.out.println(node.getKind());
    return null;
  }
  
  @Override
  public Symbols visitVariable(VariableTree node, Symbols p) {
    System.out.println("ABC" + node.getKind());
  }
}
