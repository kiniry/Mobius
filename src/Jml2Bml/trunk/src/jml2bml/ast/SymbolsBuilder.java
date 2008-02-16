package jml2bml.ast;

import jml2bml.bytecode.BytecodeUtil;
import jml2bml.symbols.Symbols;
import jml2bml.symbols.Variable;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;

import com.sun.source.tree.BlockTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;

/**
 * Builds symbol table.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public class SymbolsBuilder extends ExtendedJmlTreeScanner<Symbols, Symbols> {
  /**
   * Collection of ancestors for all AST nodes.
   */
  private final TreeNodeFinder ancestorFinder;

  /**
   * application context.
   */
  private final Context context;

  /**
   * Creates new instance of the symbol builder.
   * @param context application context
   */
  public SymbolsBuilder(final Context context) {
    ancestorFinder = context.get(TreeNodeFinder.class);
    this.context = context;
  }

  /**
   * Scans the given node. By default does nothing.
   * @param node node to scan
   * @param p symbol table containing all information gathered before this node
   * @return symbol table updated by this node
   */
  public Symbols scan(final Tree node, final Symbols p) {
    return p;
  };
  /**
   * Scans the given node. By default does nothing.
   * @param nodes nodes to scan
   * @param p symbol table containing all information gathered before this node
   * @return symbol table updated by this node
   */
  @Override
  public Symbols scan(final Iterable<? extends Tree> nodes, final Symbols p) {
    return p;
  };

  //TODO handle modifiers (static)
  /**
   * Visit the variable declaration (adds new entry to the symbol table).
   * @param node visited node
   * @param p symbol table before this node
   * @return symbol table after this node
   */
  @Override
  public Symbols visitJmlVariableDecl(final JmlVariableDecl node,
                                      final Symbols p) {
    if ("this".equals(node.name.toString())) {
      return p;
    }
    final Tree block = ancestorFinder.getAncestor(node, Tree.Kind.BLOCK);
    final Tree method = ancestorFinder.getAncestor(node, Tree.Kind.METHOD);
    if (method != null && block != null) {

      final Tree clazz = ancestorFinder.getAncestor(node, Tree.Kind.CLASS);
      if (method == ancestorFinder.getAncestor(clazz, Tree.Kind.METHOD)) {
        //field in an inner class
        handleField(node, clazz, p);
      } else {
        //local variable
        handleLocal(node, method, p);
      }
    } else if (method != null) {
      //parameter
      handleLocal(node, method, p);
    } else {
      //class field
      final Tree clazz = ancestorFinder.getAncestor(node, Tree.Kind.CLASS);
      handleField(node, clazz, p);
    }

    return p;
  }

  /**
   * Handles the local variable declaration.
   * @param node local variable declaration
   * @param method method containing this declaration
   * @param s symbol table before this declaration
   */
  private void handleLocal(final JmlVariableDecl node, final Tree method,
                           final Symbols s) {
    final BCClass cl = s.findClass();
    final BCMethod m = BytecodeUtil.findMethod(((MethodTree) method).getName(),
                                               cl);
    final LocalVariable var = m.findLocalVariable(node.name.toString());
    s.put(node.name.toString(), new Variable(var, node));
  }

  /**
   * Handles field declarations.
   * @param node field declaration
   * @param clazz class containing the field declaration
   * @param s symbol table before this node
   */
  private void handleField(final JmlVariableDecl node, final Tree clazz,
                           final Symbols s) {
    final BCClass cl = s.findClass();

    final int nameIndex = cl.getFieldIndex(node.getName().toString());
    if (nameIndex == -1) {
      //FIXME throw an exception
    }
    s.put(node.name.toString(), new Variable((FieldRef) null, node));

  }

  /**
   * Visits block node (creates new symbol table overlaping the given one).
   * @param node visited node
   * @param p symbol table before this node
   * @return updated symbol table
   */
  @Override
  public Symbols visitBlock(final BlockTree node, final Symbols p) {
    return new Symbols(p);
  }

  /**
   * Visits class declaration (creates new symbol table).
   * @param node visited node
   * @param p symbol table before this node
   * @return updated symbol table
   */
  @Override
  public Symbols visitJmlClassDecl(final JmlClassDecl node, final Symbols p) {
    final Symbols newSymbols = new Symbols(p);
    newSymbols.setClass(BytecodeUtil.createClass(node.name, context));
    return newSymbols;
  }

  /**
   * Visits method declaration (creates new symbol table).
   * @param node visited node.
   * @param p symbol table before this node
   * @return updated symbol table
   */
  @Override
  public Symbols visitJmlMethodDecl(final JmlMethodDecl node, final Symbols p) {
    return new Symbols(p);
  }
}
