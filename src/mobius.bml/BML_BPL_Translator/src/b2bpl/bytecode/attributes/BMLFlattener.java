package b2bpl.bytecode.attributes;

import org.objectweb.asm.ByteVector;
import org.objectweb.asm.ClassWriter;

import b2bpl.bytecode.JType;
import b2bpl.bytecode.bml.IBMLExpressionVisitor;
import b2bpl.bytecode.bml.IBMLStoreRefVisitor;
import b2bpl.bytecode.bml.ast.BMLArrayAccessExpression;
import b2bpl.bytecode.bml.ast.BMLArrayElementStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayLengthExpression;
import b2bpl.bytecode.bml.ast.BMLArrayAllStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayRangeStoreRef;
import b2bpl.bytecode.bml.ast.BMLBinaryArithmeticExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryBitwiseExpression;
import b2bpl.bytecode.bml.ast.BMLBinaryLogicalExpression;
import b2bpl.bytecode.bml.ast.BMLBooleanLiteral;
import b2bpl.bytecode.bml.ast.BMLBoundVariableExpression;
import b2bpl.bytecode.bml.ast.BMLCastExpression;
import b2bpl.bytecode.bml.ast.BMLElemTypeExpression;
import b2bpl.bytecode.bml.ast.BMLEqualityExpression;
import b2bpl.bytecode.bml.ast.BMLEverythingStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldAccessExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldExpression;
import b2bpl.bytecode.bml.ast.BMLFieldStoreRef;
import b2bpl.bytecode.bml.ast.BMLFreshExpression;
import b2bpl.bytecode.bml.ast.BMLInstanceOfExpression;
import b2bpl.bytecode.bml.ast.BMLIntLiteral;
import b2bpl.bytecode.bml.ast.BMLLocalVariableExpression;
import b2bpl.bytecode.bml.ast.BMLLocalVariableStoreRef;
import b2bpl.bytecode.bml.ast.BMLLogicalNotExpression;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLNullLiteral;
import b2bpl.bytecode.bml.ast.BMLOldExpression;
import b2bpl.bytecode.bml.ast.BMLPredicate;
import b2bpl.bytecode.bml.ast.BMLQuantifierExpression;
import b2bpl.bytecode.bml.ast.BMLRelationalExpression;
import b2bpl.bytecode.bml.ast.BMLResultExpression;
import b2bpl.bytecode.bml.ast.BMLStackCounterExpression;
import b2bpl.bytecode.bml.ast.BMLStackElementExpression;
import b2bpl.bytecode.bml.ast.BMLThisExpression;
import b2bpl.bytecode.bml.ast.BMLThisStoreRef;
import b2bpl.bytecode.bml.ast.BMLTypeOfExpression;
import b2bpl.bytecode.bml.ast.BMLUnaryMinusExpression;


public class BMLFlattener
    implements IBMLExpressionVisitor<Object>, IBMLStoreRefVisitor<Object> {

  private final ClassWriter writer;

  private final ByteVector bytes;

  private int insideOld = 0;

  public BMLFlattener(ClassWriter writer, ByteVector bytes) {
    this.writer = writer;
    this.bytes = bytes;
  }

  public Object visitQuantifierExpression(BMLQuantifierExpression expr) {
    switch (expr.getOperator()) {
      case FORALL:
        bytes.putByte(BMLAttributeTags.FORALL);
        break;
      case EXISTS:
      default:
        bytes.putByte(BMLAttributeTags.EXISTS);
        break;
    }

    bytes.putByte(expr.getVariableTypes().length);
    for (JType type : expr.getVariableTypes()) {
      bytes.putByte(BMLAttributeTags.JAVA_TYPE);
      bytes.putShort(writer.newClass(type.getInternalName()));
    }
    expr.getExpression().accept(this);

    return null;
  }

  public Object visitBinaryArithmeticExpression(
      BMLBinaryArithmeticExpression expr) {
    switch (expr.getOperator()) {
      case PLUS:
        bytes.putByte(BMLAttributeTags.PLUS);
        break;
      case MINUS:
        bytes.putByte(BMLAttributeTags.MINUS);
        break;
      case TIMES:
        bytes.putByte(BMLAttributeTags.TIMES);
        break;
      case DIVIDE:
        bytes.putByte(BMLAttributeTags.DIVIDE);
        break;
      case REMAINDER:
      default:
        bytes.putByte(BMLAttributeTags.REMAINDER);
        break;
    }

    expr.getLeft().accept(this);
    expr.getRight().accept(this);

    return null;
  }

  public Object visitBinaryLogicalExpression(BMLBinaryLogicalExpression expr) {
    switch (expr.getOperator()) {
      case AND:
        bytes.putByte(BMLAttributeTags.AND);
        break;
      case OR:
        bytes.putByte(BMLAttributeTags.OR);
        break;
      case IMPLIES:
        bytes.putByte(BMLAttributeTags.IMPLIES);
        break;
      case EQUIVALENCE:
      default:
        // FIXME[om]: What constant???!!!
        break;
    }

    expr.getLeft().accept(this);
    expr.getRight().accept(this);

    return null;
  }

  public Object visitEqualityExpression(BMLEqualityExpression expr) {
    switch (expr.getOperator()) {
      case EQUALS:
        bytes.putByte(BMLAttributeTags.EQUALS);
        break;
      case NOT_EQUALS:
      default:
        bytes.putByte(BMLAttributeTags.NOT_EQUALS);
        break;
    }

    expr.getLeft().accept(this);
    expr.getRight().accept(this);

    return null;
  }

  public Object visitRelationalExpression(BMLRelationalExpression expr) {
    switch (expr.getOperator()) {
      case LESS:
        bytes.putByte(BMLAttributeTags.LESS);
        break;
      case GREATER:
        bytes.putByte(BMLAttributeTags.GREATER);
        break;
      case LESS_EQUAL:
        bytes.putByte(BMLAttributeTags.LESS_EQUAL);
        break;
      case GREATER_EQUAL:
      default:
        bytes.putByte(BMLAttributeTags.GREATER_EQUAL);
        break;
    }

    expr.getLeft().accept(this);
    expr.getRight().accept(this);

    return null;
  }

  public Object visitBinaryBitwiseExpression(BMLBinaryBitwiseExpression expr) {
    switch (expr.getOperator()) {
      case SHL:
        bytes.putByte(BMLAttributeTags.SHL);
        break;
      case SHR:
        bytes.putByte(BMLAttributeTags.SHR);
        break;
      case USHR:
        bytes.putByte(BMLAttributeTags.USHR);
        break;
      case AND:
        bytes.putByte(BMLAttributeTags.BITWISE_AND);
        break;
      case OR:
        bytes.putByte(BMLAttributeTags.BITWISE_OR);
        break;
      case XOR:
      default:
        bytes.putByte(BMLAttributeTags.BITWISE_XOR);
        break;
    }

    expr.getLeft().accept(this);
    expr.getRight().accept(this);

    return null;
  }

  public Object visitUnaryMinusExpression(BMLUnaryMinusExpression expr) {
    bytes.putByte(BMLAttributeTags.UNARY_MINUS);
    expr.getExpression().accept(this);
    return null;
  }

  public Object visitLogicalNotExpression(BMLLogicalNotExpression expr) {
    bytes.putByte(BMLAttributeTags.NOT);
    expr.getExpression().accept(this);
    return null;
  }

  public Object visitInstanceOfExpression(BMLInstanceOfExpression expr) {
    bytes.putByte(BMLAttributeTags.INSTANCEOF);
    expr.getExpression().accept(this);
    bytes.putByte(BMLAttributeTags.JAVA_TYPE);
    bytes.putShort(writer.newClass(expr.getTargetType().getInternalName()));
    return null;
  }

  public Object visitCastExpression(BMLCastExpression expr) {
    bytes.putByte(BMLAttributeTags.CAST);
    bytes.putByte(BMLAttributeTags.JAVA_TYPE);
    bytes.putShort(writer.newClass(expr.getTargetType().getInternalName()));
    expr.getExpression().accept(this);
    return null;
  }

  public Object visitBooleanLiteral(BMLBooleanLiteral literal) {
    if (literal == BMLBooleanLiteral.TRUE) {
      bytes.putByte(BMLAttributeTags.TRUE);
    } else {
      bytes.putByte(BMLAttributeTags.FALSE);
    }
    return null;
  }

  public Object visitIntLiteral(BMLIntLiteral literal) {
    bytes.putByte(BMLAttributeTags.INT_LITERAL);
    bytes.putInt(literal.getValue());
    return null;
  }

  public Object visitNullLiteral(BMLNullLiteral literal) {
    bytes.putByte(BMLAttributeTags.NULL);
    return null;
  }

  public Object visitLocalVariableExpression(BMLLocalVariableExpression expr) {
    if (insideOld > 0) {
      bytes.putByte(BMLAttributeTags.OLD_LOCAL_VARIABLE);
    } else {
      bytes.putByte(BMLAttributeTags.LOCAL_VARIABLE);
    }
    bytes.putShort(expr.getIndex());
    return null;
  }

  public Object visitBoundVariableExpression(BMLBoundVariableExpression expr) {
    bytes.putByte(BMLAttributeTags.BOUND_VARIABLE);
    bytes.putShort(expr.getIndex());
    return null;
  }

  public Object visitStackElementExpression(BMLStackElementExpression expr) {
    bytes.putByte(BMLAttributeTags.STACK_ELEMENT);
    expr.getIndexExpression().accept(this);
    return null;
  }

  public Object visitStackCounterExpression(BMLStackCounterExpression expr) {
    bytes.putByte(BMLAttributeTags.STACK_COUNTER);
    return null;
  }

  public Object visitOldExpression(BMLOldExpression expr) {
    insideOld++;
    expr.getExpression().accept(this);
    insideOld--;
    return null;
  }

  public Object visitPredicate(BMLPredicate predicate) {
    predicate.getExpression().accept(this);
    return null;
  }

  public Object visitFieldExpression(BMLFieldExpression expr) {
    if (insideOld > 0) {
      if (expr.isGhostField()) {
        bytes.putByte(BMLAttributeTags.OLD_MODEL_FIELD);
      } else {
        bytes.putByte(BMLAttributeTags.OLD_FIELD);
      }
    } else {
      if (expr.isGhostField()) {
        bytes.putByte(BMLAttributeTags.MODEL_FIELD);
      } else {
        bytes.putByte(BMLAttributeTags.FIELD);
      }
    }

    int cpIndex = writer.newField(
        expr.getFieldOwner().getInternalName(),
        expr.getFieldName(),
        expr.getFieldDescriptor());
    bytes.putShort(cpIndex);

    return null;
  }

  public Object visitFieldAccessExpression(BMLFieldAccessExpression expr) {
    bytes.putByte(BMLAttributeTags.FIELD_ACCESS);
    expr.getPrefix().accept(this);
    expr.getFieldReference().accept(this);
    return null;
  }

  public Object visitArrayAccessExpression(BMLArrayAccessExpression expr) {
    bytes.putByte(BMLAttributeTags.ARRAY_ACCESS);
    expr.getPrefix().accept(this);
    expr.getIndex().accept(this);
    return null;
  }

  public Object visitArrayLengthExpression(BMLArrayLengthExpression expr) {
    bytes.putByte(BMLAttributeTags.FIELD_ACCESS);
    expr.getPrefix().accept(this);
    bytes.putByte(BMLAttributeTags.ARRAY_LENGTH);
    return null;
  }

  public Object visitTypeOfExpression(BMLTypeOfExpression expr) {
    bytes.putByte(BMLAttributeTags.TYPE_OF);
    expr.getExpression().accept(this);
    return null;
  }

  public Object visitElemTypeExpression(BMLElemTypeExpression expr) {
    bytes.putByte(BMLAttributeTags.ELEM_TYPE);
    expr.getTypeExpression().accept(this);
    return null;
  }

  public Object visitResultExpression(BMLResultExpression expr) {
    bytes.putByte(BMLAttributeTags.RESULT);
    return null;
  }

  public Object visitThisExpression(BMLThisExpression expr) {
    if (insideOld > 0) {
      bytes.putByte(BMLAttributeTags.OLD_THIS);
    } else {
      bytes.putByte(BMLAttributeTags.THIS);
    }
    return null;
  }

  public Object visitFreshExpression(BMLFreshExpression expr) {
    // REVIEW[om]: Not supported by JACK yet.
    throw new RuntimeException("no encoding of \\fresh expression supported");
  }

  public Object visitEverythingStoreRef(BMLEverythingStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_EVERYTHING);
    return null;
  }

  public Object visitNothingStoreRef(BMLNothingStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_NOTHING);
    return null;
  }

  public Object visitThisStoreRef(BMLThisStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.THIS);
    return null;
  }

  public Object visitLocalVariableStoreRef(BMLLocalVariableStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_IDENT);
    bytes.putByte(BMLAttributeTags.LOCAL_VARIABLE);
    bytes.putShort(storeRef.getIndex());
    return null;
  }

  public Object visitFieldStoreRef(BMLFieldStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_IDENT);
    if (storeRef.isGhostField()) {
      bytes.putByte(BMLAttributeTags.MODEL_FIELD);
    } else {
      bytes.putByte(BMLAttributeTags.FIELD);
    }

    int cpIndex = writer.newField(
        storeRef.getFieldOwner().getInternalName(),
        storeRef.getFieldName(),
        storeRef.getFieldDescriptor());
    bytes.putShort(cpIndex);

    return null;
  }

  public Object visitFieldAccessStoreRef(BMLFieldAccessStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_DOT);
    storeRef.getField().accept(this);
    storeRef.getPrefix().accept(this);
    return null;
  }

  public Object visitArrayElementStoreRef(BMLArrayElementStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY);
    storeRef.getPrefix().accept(this);
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY_INDEX);
    storeRef.getIndex().accept(this);
    return null;
  }

  public Object visitArrayAllStoreRef(BMLArrayAllStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY);
    storeRef.getPrefix().accept(this);
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY_ALL);
    return null;
  }

  public Object visitArrayRangeStoreRef(BMLArrayRangeStoreRef storeRef) {
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY);
    storeRef.getPrefix().accept(this);
    bytes.putByte(BMLAttributeTags.MODIFIES_ARRAY_INTERVAL);
    storeRef.getStartIndex().accept(this);
    storeRef.getEndIndex().accept(this);
    return null;
  }
}
