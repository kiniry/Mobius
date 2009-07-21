package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.BooleanConstant;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.source.SourceLocation;

import java.io.PrintStream;
import java.util.List;

public class PrettyPrintVisitor extends AbstractVisitor implements IVisitor {

  private final TextPrinter tp;
  
  public PrettyPrintVisitor(PrintStream ps) {
    tp = new TextPrinter(ps);
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node,
      List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    if (indexing != null) {
      indexing.accept(this);
      tp.printLine();
    }
    for (SpecificationElement spec : bonSpecification) {
      spec.accept(this);
    }
  }

  @Override
  public void visitBooleanConstant(BooleanConstant node, Boolean value, SourceLocation loc) {
    tp.print(value.toString());
  }

  @Override
  public void visitClassName(ClassName node, String name, SourceLocation loc) {
    tp.print(name);
  }

  @Override
  public void visitClazz(Clazz node, ClassName name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {
    tp.print(toString(mod));
    tp.print(name.getName());
    
    if (generics != null && generics.size() > 0) {
      //TODO print list of...
    } else {
      tp.print(" ");
    }
    if (reused) {
      tp.print("reused ");
    }
    if (persistent) {
      tp.print("persistent ");
    }
    if (interfaced) {
      tp.print("interfaced ");
    }
    tp.printLine();
    printComment(comment);
    visitNodeIfNonNull(classInterface);
  }

  
  protected String toString(KeywordConstant.Constant constant) {
    switch (constant) {
    case CURRENT:
      return "Current";
    case VOID:
      return "Void";
    }
    return "";
  }
  
  protected String toString(Clazz.Mod modifier) {
    switch (modifier) {
    case DEFERRED:
      return "deferred ";
    case EFFECTIVE:
      return "effective ";
    case ROOT:
      return "root ";
    default:
      return "";
    }
  }
  
  protected void printComment(String commentText) {
    if (commentText != null) {
      tp.printLine("--" + commentText);
    }
  }
  
  protected final void visitNodeIfNonNull(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }
}
