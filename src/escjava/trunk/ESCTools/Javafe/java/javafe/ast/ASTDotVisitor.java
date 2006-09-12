/**
 * ASTDotVisitor.java
 *
 * @title "AST DOT file visitor"
 * @description "Walks through an AST and outputs a dot graph format representation of that AST"
 * @
 */

package javafe.ast;

import java.io.Writer;
import java.io.FileWriter;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import javafe.util.Location;
import java.util.StringTokenizer;

public class ASTDotVisitor extends Visitor {
  
  /**
   * our means of outputting the dot representation of the AST 
   */
  private FileWriter out = null;
  
  /**
   * a means of getting source text from the pretty printer
   */
  private ByteArrayOutputStream source_dump = null;
  
  /**
   * stores result of the last visit method call
   */
  private String visit_string = "";
  
  /**
   * pretty printer for extracting our source text
   */
  private StandardPrettyPrint printer = null;
  
  /**
   * Sets up the visit string for writing to a dot file with the given
   * source text, dotId and node type. This will also reset the buffer which
   * the pretty printer writes to.
   */
  private void setVisitString(String source_text, int dotId, String type) {
    // set the string
    visit_string = '"' + "" + dotId + " " + type + " " + source_text + '"';
    // reset the buffer
    source_dump.reset();
  }
  
  /**
   * recurses through the tree and writes the dotfile representation of it. if
   * parent is null this is the root of the tree. current is the node we are
   * parsing.
   */
  private void writeDot(ASTNode parent, ASTNode current) {
    // if this node is the root of the tree start the recursion otherwise make
    // the links between this node and its parent then do the recursive call
    // on the children
    if(parent != null) {
      // contains the id and type of the parent node
      String parent_representation;
      // contains the id and type of this node
      String current_representation;
      // call the visitor on parent and current and retrieve the string descriptions
      parent.accept(this);
      parent_representation = visit_string;
      current.accept(this);
      current_representation = visit_string;
      // make the link in the file
      try {
        out.write("  " + parent_representation + " -> " + current_representation + "\n");
      } catch (IOException exception) {
        System.out.println("failed to write to file");
      }
    }
    // do the recursive call on the children provided the child is an ASTNode
    for(int count = 0; count < current.childCount(); count++) {
      Object o = current.childAt(count);
      if(o instanceof ASTNode) writeDot(current, (ASTNode) o);
    }
  }
  
  /**
   * constructor that takes in a compilation unit that represents a class
   * and initalizes a filewriter in the directory escjava is called from
   */
  public ASTDotVisitor() {
    // holds the value of this node so when we do recursive calls we can make
    // the correct edges in the graph
    //
    // try opening the file for now throw a message out if it fails
    try {
      out = new FileWriter("Test.dot");
    } catch(IOException exception) {
      System.out.println("could not open file");
    }
    // init source_dump and printer
    source_dump = new ByteArrayOutputStream();
    printer = new StandardPrettyPrint();
  }
  
  /**
   * visits an ast node and outputs it in dot file format
   */
  //@ requires x != null;
  public void visitASTNode(ASTNode x) {
    // write the file
    try {
      // write the start of the dot file
      out.write("digraph Test {\n");
      // call the recursive method on x
      writeDot(null, x);
      // write the end of the dot file
      out.write("}\n");
      out.close();
    } catch(IOException exception) {
      System.out.println("failed to write to file");
    }
  }
  
  //@ requires x != null;
  public void visitCompilationUnit(CompilationUnit x) {
    setVisitString("", x.dotId, "CompilationUnit(todo)");
  }
  
  //@ requires x != null;
  public void visitImportDecl(ImportDecl x) {
    setVisitString("", x.dotId, "ImportDecl(have not seen yet)");
  }
  
  //@ requires x != null
  public void visitSingleTypeImportDecl(SingleTypeImportDecl x) {
    setVisitString("", x.dotId, "SingleTypeImportDecl(todo)");
  }
  
  //@ requires x != null;
  public void visitOnDemandImportDecl(OnDemandImportDecl x) {
    setVisitString("", x.dotId, "OnDemandImportDecl(todo)");
  }

  //@ requires x != null;
  public void visitTypeDecl(TypeDecl x) {
    // get the source text
    printer.print(source_dump, 0, x);
  }

  //@ requires x != null;
  public void visitClassDecl(ClassDecl x) {
    visitTypeDecl(x);
    // we need to grab everything before the first { charcter and remove
    // all the newlines
    String source = source_dump.toString();
    char[] source_array = source.substring(0, source.indexOf('{')).toCharArray();
    for(int count = 0; count < source_array.length; count++) {
      if(source_array[count] == '\n') source_array[count] = ' ';
    }
    source = new String(source_array);
    setVisitString(source, x.dotId, "ClassDecl");
  }

  //@ requires x != null;
  public void visitInterfaceDecl(InterfaceDecl x) {
    visitTypeDecl(x);
    // we have to be pretty careful here as we can have interfaces that extend
    // other interfaces so we need to get everything before the first {
    // charcter. we also need to replace the newline charcters as well
    String source = source_dump.toString();
    char[] source_array = source.substring(0, source.indexOf('{')).toCharArray();
    for(int count = 0; count < source_array.length; count++) {
      if(source_array[count] == '\n') source_array[count] = ' ';
    }
    source = new String(source_array);
    setVisitString(source, x.dotId, "InterfaceDecl");
  }

  //@ requires x != null;
  public void visitRoutineDecl(RoutineDecl x) {
  }

  //@ requires x != null;
  public void visitConstructorDecl(ConstructorDecl x) {
    // grab the source text
    printer.print(source_dump, 0, x, x.id(), false);
    // get everything before the first newline
    String source = source_dump.toString().substring(0,source_dump.toString().indexOf('\n'));
    setVisitString(source, x.dotId, "ConstructorDecl");
  }

  //@ requires x != null;
  public void visitMethodDecl(MethodDecl x) {
    // grab the source text
    printer.print(source_dump, 0, x, x.id(), false);
    // grab everything before the first newline
    String source = source_dump.toString().substring(0,source_dump.toString().indexOf('\n'));
    setVisitString(source, x.dotId, "MethodDecl");
  }

  //@ requires x != null;
  public void visitInitBlock(InitBlock x) {
    setVisitString("", x.dotId, "InitBlock(have not seen yet)");
  }

  //@ requires x != null;
  public void visitTypeDeclElemPragma(TypeDeclElemPragma x) {
    setVisitString("", x.dotId, "TypeDeclElemPragma(have not seen yet)");
  }

  //@ requires x != null;
  public void visitGenericVarDecl(GenericVarDecl x) {
    // get the source text
    printer.print(source_dump, x);
  }

  //@ requires x != null;
  public void visitLocalVarDecl(LocalVarDecl x) {
    visitGenericVarDecl(x);
    setVisitString(source_dump.toString(), x.dotId, "LocalVarDecl");
  }

  //@ requires x != null;
  public void visitFieldDecl(FieldDecl x) {
    visitGenericVarDecl(x);
    setVisitString(source_dump.toString(), x.dotId, "FieldDecl");
  }

  //@ requires x != null;
  public void visitFormalParaDecl(FormalParaDecl x) {
    visitGenericVarDecl(x);
    setVisitString(source_dump.toString(), x.dotId, "FormalParaDecl");
  }

  //@ requires x != null;
  public void visitStmt(Stmt x) {
    // grab the source text
    printer.print(source_dump, 0, x);
  }

  //@ requires x != null;
  public void visitGenericBlockStmt(GenericBlockStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitBlockStmt(BlockStmt x) {
    visitGenericBlockStmt(x);
    setVisitString("", x.dotId, "BlockStmt");
  }

  //@ requires x != null;
  public void visitSwitchStmt(SwitchStmt x) {
    visitStmt(x);
    // grab everything the first occurence of the ) charcter searching
    // backwards from the first newline
    String source = source_dump.toString();
    source = source.substring(0, source.lastIndexOf(')', source.indexOf('\n')) + 1);
    setVisitString(source, x.dotId, "SwitchStmt");
  }

  //@ requires x != null;
  public void visitAssertStmt(AssertStmt x) {
    setVisitString("", x.dotId, "AssertStmt(have not seen yet)");
  }

  //@ requires x != null;
  public void visitVarDeclStmt(VarDeclStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "VarDeclStmt");
  }

  //@ requires x != null;
  public void visitClassDeclStmt(ClassDeclStmt x) {
    setVisitString("", x.dotId, "ClassDeclStmt(have not seen yet)");
  }

  //@ requires x != null;
  public void visitWhileStmt(WhileStmt x) {
    visitStmt(x);
    // grab everything from the start of the while statment to the last )
    // charcter from the first newline
    String source = source_dump.toString();
    source = source.substring(0, source.lastIndexOf(')', source.indexOf('\n')) + 1);
    setVisitString(source, x.dotId, "WhileStmt");
  }

  //@ requires x != null;
  public void visitDoStmt(DoStmt x) {
    visitStmt(x);
    setVisitString("", x.dotId, "DoStmt");
  }

  //@ requires x != null;
  public void visitSynchronizeStmt(SynchronizeStmt x) {
    setVisitString("", x.dotId, "SynchronizeStmt(have not seen yet)");
  }

  //@ requires x != null;
  public void visitEvalStmt(EvalStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "EvalStmt");
  }

  //@ requires x != null;
  public void visitReturnStmt(ReturnStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "ReturnStmt");
  }

  //@ requires x != null;
  public void visitThrowStmt(ThrowStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "ThrowStmt");
  }

  //@ requires x != null;
  public void visitBranchStmt(BranchStmt x) {
    setVisitString("", x.dotId, "BranchStmt(have not seen yet)");
  }

  //@ requires x != null;
  public void visitBreakStmt(BreakStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "BreakStmt");
  }

  //@ requires x != null;
  public void visitContinueStmt(ContinueStmt x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "ContinueStmt");
  }

  //@ requires x != null;
  public void visitLabelStmt(LabelStmt x) {
    setVisitString("", x.dotId, "LabelStmt(have not seen yet)");
  }

  //@ requires x != null;
  public void visitIfStmt(IfStmt x) {
    setVisitString("", x.dotId, "IfStmt");
  }

  //@ requires x != null;
  public void visitForStmt(ForStmt x) {
    visitStmt(x);
    // get everything from the beginning until the last ) charcter is
    // encountered on the first line
    String source = source_dump.toString();
    source = source.substring(0, source.lastIndexOf(')', source.indexOf('\n')) + 1);
    setVisitString(source, x.dotId, "ForStmt");
  }

  //@ requires x != null;
  public void visitSkipStmt(SkipStmt x) {
    visitStmt(x);
    setVisitString("", x.dotId, "SkipStmt");
  }

  //@ requires x != null;
  public void visitSwitchLabel(SwitchLabel x) {
    // source string to append to the node label
    String source = null;
    visitStmt(x);
    // we must remove the new line from the label if there is one
    if(source_dump.toString().indexOf('\n') != -1) source = source_dump.toString().substring(0, source_dump.toString().indexOf('\n'));
    else source = source_dump.toString();
    setVisitString(source, x.dotId, "SwitchLabel");
  }

  //@ requires x != null;
  public void visitTryFinallyStmt(TryFinallyStmt x) {
    visitStmt(x.finallyClause);
    setVisitString("", x.dotId, "TryFinallyStmt");
  }

  //@ requires x != null;
  public void visitTryCatchStmt(TryCatchStmt x) {
    visitStmt(x);
    // grab the try statment before the first { charcter
    String source = source_dump.toString();
    source = source.substring(0, source.indexOf('{'));
    setVisitString(source, x.dotId, "TryCatchStmt");
  }

  //@ requires x != null;
  public void visitStmtPragma(StmtPragma x) {
    setVisitString("", x.dotId, "StmtPragma(have not seen yet)");
  }

  //@ requires x != null;
  public void visitConstructorInvocation(ConstructorInvocation x) {
    visitStmt(x);
    setVisitString(source_dump.toString(), x.dotId, "ConstructorInvocation");
  }

  //@ requires x != null;
  public void visitCatchClause(CatchClause x) {
    // we have to do some manual work here as the catch clause is not
    // really dealt with on its own in the pretty printer.
    printer.print(source_dump, x.arg);
    
    setVisitString("catch (" + source_dump.toString() + ")", x.dotId, "CatchClause");
  }

  //@ requires x != null;
  public void visitVarInit(VarInit x) {
    // get the source text
    printer.print(source_dump, 0, x);
  }

  //@ requires x != null;
  public void visitArrayInit(ArrayInit x) {
    visitVarInit(x);
    setVisitString(source_dump.toString(), x.dotId, "ArrayInit");
  }

  //@ requires x != null;
  public void visitExpr(Expr x) {
    // grab the source text
    printer.print(source_dump, 0, x);
  }

  //@ requires x != null;
  public void visitThisExpr(ThisExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "ThisExpr");
  }

  //@ requires x != null;
  public void visitLiteralExpr(LiteralExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "LiteralExpr");
  }

  //@ requires x != null;
  public void visitArrayRefExpr(ArrayRefExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "ArrayRefExpr");
  }

  //@ requires x != null;
  public void visitNewInstanceExpr(NewInstanceExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "NewInstanceExpr");
  }

  //@ requires x != null;
  public void visitNewArrayExpr(NewArrayExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "NewArrayExpr");
  }

  //@ requires x != null;
  public void visitCondExpr(CondExpr x) {
    setVisitString("", x.dotId, "CondExpr(have not seen yet)");
  }

  //@ requires x != null;
  public void visitInstanceOfExpr(InstanceOfExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "InstanceOfExpr");
  }

  //@ requires x != null;
  public void visitCastExpr(CastExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "CastExpr");
  }

  //@ requires x != null;
  public void visitBinaryExpr(BinaryExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "BinaryExpr");
  }

  //@ requires x != null;
  public void visitUnaryExpr(UnaryExpr x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "UnaryExpr");
  }

  //@ requires x != null;
  public void visitParenExpr(ParenExpr x) {
    setVisitString("", x.dotId, "ParenExpr(have not seen yet)");
  }

  //@ requires x != null;
  public void visitAmbiguousVariableAccess(AmbiguousVariableAccess x) {
    setVisitString("", x.dotId, "AmbiguousVariableAccess(have not seen yet)");
  }

  //@ requires x != null;
  public void visitVariableAccess(VariableAccess x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "VariableAccess");
  }

  //@ requires x != null;
  public void visitFieldAccess(FieldAccess x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "FieldAccess");
  }

  //@ requires x != null;
  public void visitAmbiguousMethodInvocation(AmbiguousMethodInvocation x) {
    setVisitString("", x.dotId, "AmbigousMethodInvocation(have not seen yet)");
  }

  //@ requires x != null;
  public void visitMethodInvocation(MethodInvocation x) {
    visitExpr(x);
    setVisitString(source_dump.toString(), x.dotId, "MethodInvocation");
  }

  //@ requires x != null;
  public void visitClassLiteral(ClassLiteral x) {
    setVisitString("", x.dotId, "ClassLiteral(have not seen yet)");
  }

  //@ requires x != null;
  public void visitObjectDesignator(ObjectDesignator x) {
    // get the source text
    printer.print(source_dump, 0, x);
  }

  //@ requires x != null;
  public void visitExprObjectDesignator(ExprObjectDesignator x) {
    visitObjectDesignator(x);
    setVisitString(source_dump.toString(), x.dotId, "ExprObjectDesignator");
  }

  //@ requires x != null;
  public void visitTypeObjectDesignator(TypeObjectDesignator x) {
    visitObjectDesignator(x);
    setVisitString("", x.dotId, "TypeObjectDesignator");
  }

  //@ requires x != null;
  public void visitSuperObjectDesignator(SuperObjectDesignator x) {
    visitObjectDesignator(x);
    setVisitString(source_dump.toString(), x.dotId, "SuperObjectDesignator");
  }

  //@ requires x != null;
  public void visitType(Type x) {
    // get the source text and set the visit string
    printer.print(source_dump, x);
    setVisitString(source_dump.toString(), x.dotId, "Type");
  }

  //@ requires x != null;
  public void visitErrorType(ErrorType x) {
    setVisitString("", x.dotId, "ErrorType(have not seen yet)");
  }

  //@ requires x != null;
  public void visitPrimitiveType(PrimitiveType x) {
    // grab the source text as a Type node can appear in the tree
    printer.print(source_dump, x);
    setVisitString(source_dump.toString(), x.dotId, "PrimitiveType");
  }

  //@ requires x != null;
  public void visitTypeName(TypeName x) {
    // grab the source text as the generic Type can appear in the tree
    printer.print(source_dump, x);
    setVisitString(source_dump.toString(), x.dotId, "TypeName");
  }

  //@ requires x != null;
  public void visitArrayType(ArrayType x) {
    // grab the source text as the generic Type can be in the tree as well
    printer.print(source_dump, x);
    setVisitString(source_dump.toString(), x.dotId, "ArrayType");
  }

  //@ requires x != null;
  public void visitName(Name x) {
    // grab the source text
    printer.print(source_dump, x);
  }

  //@ requires x != null;
  public void visitSimpleName(SimpleName x) {
    visitName(x);
    setVisitString(source_dump.toString(), x.dotId, "SimpleName");
  }

  //@ requires x != null;
  public void visitCompoundName(CompoundName x) {
    visitName(x);
    setVisitString(source_dump.toString(), x.dotId, "CompoundName");
  }

  //@ requires x != null;
  public void visitModifierPragma(ModifierPragma x) {
    setVisitString("", x.dotId, "ModifierPragma(have not seen yet)");
  }

  //@ requires x != null;
  public void visitLexicalPragma(LexicalPragma x) {
    setVisitString("", x.dotId, "LexicalPragma(have not seen yet)");
  }

  //@ requires x != null;
  public void visitTypeModifierPragma(TypeModifierPragma x) {
    setVisitString("", x.dotId, "TypeModifierPragma(have not seen yet)");
  }
  
}
