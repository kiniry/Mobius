package ie.ucd.bon.printer;

import java.io.PrintStream;

import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.IVisitorWithAdditions;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.BinaryExp.Op;
import ie.ucd.bon.ast.Quantification.Quantifier;

public class PrintVisitor extends AbstractVisitorWithAdditions implements IVisitorWithAdditions {

  protected final TextPrinter tp;
  
  public PrintVisitor(PrintStream ps) {
    tp = new TextPrinter(ps);
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

  protected void printUnaryExpOp(ie.ucd.bon.ast.UnaryExp.Op op) {
    switch (op) {
    case ADD:
      tp.print('+');
      break;
    case DELTA:
      tp.print("delta");
      break;
    case NOT:
      tp.print("not");
      break;
    case OLD:
      tp.print("old");
      break;
    case SUB:
      tp.print('-');
      break;
    }
  }

  protected void printBinaryExpOp(Op op) {
    switch (op) {
    case ADD:
      tp.print('+');
      break;
    case AND:
      tp.print("and");
      break;
    case DIV:
      tp.print('/');
      break;
    case EQ:
      tp.print('=');
      break;
    case EQUIV:
      tp.print("<->");
      break;
    case GE:
      tp.print(">=");
      break;
    case GT:
      tp.print('>');
      break;
    case HASTYPE:
      tp.print(':');
      break;
    case IMPLIES:
      tp.print("->");
      break;
    case INTDIV:
      tp.print("//");
      break;
    case LE:
      tp.print("<=");
      break;
    case LT:
      tp.print('<');
      break;
    case MEMBEROF:
      tp.print("member_of");
      break;
    case MOD:
      tp.print("\\\\");
      break;
    case MUL:
      tp.print('*');
      break;
    case NEQ:
      tp.print("/=");
      break;
    case NOTMEMBEROF:
      tp.print("not member_of");
      break;
    case OR:
      tp.print("or");
      break;
    case POW:
      tp.print('^');
      break;
    case SUB:
      tp.print('-');
      break;
    case XOR:
      tp.print("xor");
      break;
    }
  }

  protected void printQuantifier(Quantifier quantifier) {
    switch (quantifier) {
    case EXISTS:
      tp.print("exists");
      break;
    case FORALL:
      tp.print("for_all");
      break;
    }
  }

  protected final void visitNodeIfNonNull(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }

}
