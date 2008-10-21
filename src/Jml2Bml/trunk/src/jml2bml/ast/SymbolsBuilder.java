package jml2bml.ast;

import java.util.HashMap;
import java.util.Map;

import jml2bml.bmllib.ConstantPoolHelper;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.symbols.Symbols;
import jml2bml.symbols.Variable;
import jml2bml.utils.JCUtils;

import org.apache.bcel.generic.LocalVariableGen;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;
import annot.bcexpression.javatype.JavaType;

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
  private final Context myContext;

  /**
   * Creates new instance of the symbol builder.
   * @param context application context
   */
  public SymbolsBuilder(final Context context) {
    ancestorFinder = context.get(TreeNodeFinder.class);
    this.myContext = context;
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
    final boolean isGhost = JCUtils.isGhost(node);
    final boolean isModal = JCUtils.isModal(node);
    final Tree block = ancestorFinder.getAncestor(node, Tree.Kind.BLOCK);
    final Tree method = ancestorFinder.getAncestor(node, Tree.Kind.METHOD);
    if (method != null && block != null) {

      final Tree clazz = ancestorFinder.getAncestor(node, Tree.Kind.CLASS);
      if (method == ancestorFinder.getAncestor(clazz, Tree.Kind.METHOD)
          || isGhost || isModal) {
        //field in an inner class
        handleField(node, clazz, p, isGhost, isModal);
      } else {
        //local variable
        handleLocal(node, method, p);
      }
    } else if (method != null && !isGhost && !isModal) {
      //parameter
      
      handleLocal(node, method, p);
    } else {
      //class field
      final Tree clazz = ancestorFinder.getAncestor(node, Tree.Kind.CLASS);
      handleField(node, clazz, p, isGhost, isModal);
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
    System.out.println(node.name.toString());
    final BCClass cl = s.findClass();
    final BCMethod m = BytecodeUtil.findMethod(((MethodTree) method).getName(),
                                               cl);
    
    LocalVariable var = m.findLocalVariable(node.name.toString());
    if (var == null){
      int index = getIndex(m, node.getName().toString());
      LocalVariableGen lvGen = new LocalVariableGen(index, null, m.getBcelMethod().getArgumentType(index - 1), null, null);
      var = new LocalVariable(false, m, index, node.getName().toString(), lvGen);
    }
    s.put(node.name.toString(), new Variable(var, node));
  }

  int index = 0;
  BCMethod currentMethod = null;
  Map<String, Integer> mapping = null;
  private int getIndex(BCMethod m, String name){
    if (! m.equals(currentMethod)){
      index = 0;
      currentMethod = m;
      mapping = new HashMap<String, Integer>();
    }
    if (mapping.containsKey(name))
      return mapping.get(name).intValue();
    index++;
    mapping.put(name, Integer.valueOf(index));
    System.err.println("mapowanie " + name + " " + index);
    return index;
  }
  /**
   * Handles field declarations.
   * @param node field declaration
   * @param clazz class containing the field declaration
   * @param s symbol table before this node
   * @param isGhost indicates if the field is ghost
   * @param isModal indicates if the field is modal
   */
  private void handleField(final JmlVariableDecl node, final Tree clazz,
                           final Symbols s, final boolean isGhost,
                           final boolean isModal) {
    final BCClass cl = s.findClass();

    final int nameIndex = cl.getFieldIndex(node.getName().toString());
    if (nameIndex == -1) {
      //unknown field. If it is ghost, create new constant, else throw an exc.
      if (isGhost) {
        final String name = node.getName().toString();
        final String type = JavaType.getJavaType(node.getType().toString())
            .toString();

        ConstantPoolHelper.addGhostField(type, name, s);
      } else {
        throw new Jml2BmlException("Unknown field: " + node.getName());
      }
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
    newSymbols.setClass(BytecodeUtil.createClass(node.name, myContext));
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
