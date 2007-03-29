package b2bpl.bytecode.attributes;

import org.objectweb.asm.ClassReader;

import b2bpl.bytecode.B2BPLMessages;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TroubleException;
import b2bpl.bytecode.TroubleMessage;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.bml.ast.BMLArrayAccessExpression;
import b2bpl.bytecode.bml.ast.BMLArrayAllStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayElementStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayLengthExpression;
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
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessExpression;
import b2bpl.bytecode.bml.ast.BMLFieldAccessStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldExpression;
import b2bpl.bytecode.bml.ast.BMLFieldStoreRef;
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
import b2bpl.bytecode.bml.ast.BMLStoreRef;
import b2bpl.bytecode.bml.ast.BMLThisExpression;
import b2bpl.bytecode.bml.ast.BMLThisStoreRef;
import b2bpl.bytecode.bml.ast.BMLTypeOfExpression;
import b2bpl.bytecode.bml.ast.BMLUnaryMinusExpression;


public class BMLAttributeReader {

  private final ClassReader classReader;

  private final int end;

  private int current;

  private final char[] buffer;

  public BMLAttributeReader(
      ClassReader classReader,
      int offset,
      int length,
      char[] buffer) {
    this.classReader = classReader;
    this.current = offset;
    this.end = offset + length;
    this.buffer = buffer;
  }

  private void notifyUnexpectedTag(int tag) throws TroubleException {
    if (BMLAttributeTags.NAMES[tag] == null) {
      throw new TroubleException(new TroubleMessage(
          B2BPLMessages.UNKNOWN_SPECIFICATION_TAG,
          "0x" + Integer.toHexString(tag).toUpperCase()));
    } else {
      throw new TroubleException(new TroubleMessage(
          B2BPLMessages.UNEXPECTED_SPECIFICATION_TAG,
          "0x" + Integer.toHexString(tag).toUpperCase(),
          BMLAttributeTags.NAMES[tag]));
    }
  }

  public BMLExpression readExpression() throws TroubleException {
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.TRUE:
        return BMLBooleanLiteral.TRUE;
      case BMLAttributeTags.FALSE:
        return BMLBooleanLiteral.FALSE;
      case BMLAttributeTags.FORALL:
        return readQuantExpression(BMLQuantifierExpression.Operator.FORALL);
      case BMLAttributeTags.EXISTS:
        return readQuantExpression(BMLQuantifierExpression.Operator.EXISTS);
      case BMLAttributeTags.AND:
        return new BMLBinaryLogicalExpression(
            BMLBinaryLogicalExpression.Operator.AND,
            readExpression(),
            readExpression());
      case BMLAttributeTags.OR:
        return new BMLBinaryLogicalExpression(
            BMLBinaryLogicalExpression.Operator.OR,
            readExpression(),
            readExpression());
      case BMLAttributeTags.IMPLIES:
        return new BMLBinaryLogicalExpression(
            BMLBinaryLogicalExpression.Operator.IMPLIES,
            readExpression(),
            readExpression());
      case BMLAttributeTags.EQUALS:
        return new BMLEqualityExpression(
            BMLEqualityExpression.Operator.EQUALS,
            readExpression(),
            readExpression());
      case BMLAttributeTags.NOT_EQUALS:
        return new BMLEqualityExpression(
            BMLEqualityExpression.Operator.NOT_EQUALS,
            readExpression(),
            readExpression());
      case BMLAttributeTags.GREATER:
        return new BMLRelationalExpression(
            BMLRelationalExpression.Operator.GREATER,
            readExpression(),
            readExpression());
      case BMLAttributeTags.LESS:
        return new BMLRelationalExpression(
            BMLRelationalExpression.Operator.LESS,
            readExpression(),
            readExpression());
      case BMLAttributeTags.LESS_EQUAL:
        return new BMLRelationalExpression(
            BMLRelationalExpression.Operator.LESS_EQUAL,
            readExpression(),
            readExpression());
      case BMLAttributeTags.GREATER_EQUAL:
        return new BMLRelationalExpression(
            BMLRelationalExpression.Operator.GREATER_EQUAL,
            readExpression(),
            readExpression());
      case BMLAttributeTags.PLUS:
        return new BMLBinaryArithmeticExpression(
            BMLBinaryArithmeticExpression.Operator.PLUS,
            readExpression(),
            readExpression());
      case BMLAttributeTags.MINUS:
        return new BMLBinaryArithmeticExpression(
            BMLBinaryArithmeticExpression.Operator.MINUS,
            readExpression(),
            readExpression());
      case BMLAttributeTags.TIMES:
        return new BMLBinaryArithmeticExpression(
            BMLBinaryArithmeticExpression.Operator.TIMES,
            readExpression(),
            readExpression());
      case BMLAttributeTags.DIVIDE:
        return new BMLBinaryArithmeticExpression(
            BMLBinaryArithmeticExpression.Operator.DIVIDE,
            readExpression(),
            readExpression());
      case BMLAttributeTags.REMAINDER:
        return new BMLBinaryArithmeticExpression(
            BMLBinaryArithmeticExpression.Operator.REMAINDER,
            readExpression(),
            readExpression());
      case BMLAttributeTags.SHL:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.SHL,
            readExpression(),
            readExpression());
      case BMLAttributeTags.SHR:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.SHR,
            readExpression(),
            readExpression());
      case BMLAttributeTags.USHR:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.USHR,
            readExpression(),
            readExpression());
      case BMLAttributeTags.BITWISE_AND:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.AND,
            readExpression(),
            readExpression());
      case BMLAttributeTags.BITWISE_OR:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.OR,
            readExpression(),
            readExpression());
      case BMLAttributeTags.BITWISE_XOR:
        return new BMLBinaryBitwiseExpression(
            BMLBinaryBitwiseExpression.Operator.XOR,
            readExpression(),
            readExpression());
      case BMLAttributeTags.UNARY_MINUS:
        return new BMLUnaryMinusExpression(readExpression());
      case BMLAttributeTags.NOT:
        return new BMLLogicalNotExpression(readExpression());
      case BMLAttributeTags.INSTANCEOF: {
        BMLExpression expression = readExpression();
        // Skip the byte encoding the type.
        readByte();
        JType type = readType();
        return new BMLInstanceOfExpression(expression, type);
      }
      case BMLAttributeTags.CAST: {
        // Skip the byte encoding the type.
        readByte();
        JType type = readType();
        BMLExpression expression = readExpression();
        return new BMLCastExpression(type, expression);
      }
      case BMLAttributeTags.INT_LITERAL:
        return new BMLIntLiteral(readInt());
      case BMLAttributeTags.NULL:
        return BMLNullLiteral.NULL;
      case BMLAttributeTags.RESULT:
        return BMLResultExpression.RESULT;
      case BMLAttributeTags.FIELD_ACCESS:
        return readFieldAccessExpression();
      case BMLAttributeTags.ARRAY_ACCESS:
        return readArrayAccessExpression();
      case BMLAttributeTags.TYPE_OF:
        return new BMLTypeOfExpression(readExpression());
      case BMLAttributeTags.ELEM_TYPE:
        return new BMLElemTypeExpression(readExpression());
      case BMLAttributeTags.THIS:
        return BMLThisExpression.THIS;
      case BMLAttributeTags.OLD_THIS:
        return new BMLOldExpression(BMLThisExpression.THIS);
      case BMLAttributeTags.FIELD:
        return readFieldExpression(false);
      case BMLAttributeTags.OLD_FIELD:
        return new BMLOldExpression(readFieldExpression(false));
      case BMLAttributeTags.MODEL_FIELD:
        return readFieldExpression(true);
      case BMLAttributeTags.OLD_MODEL_FIELD:
        return new BMLOldExpression(readFieldExpression(true));
      case BMLAttributeTags.LOCAL_VARIABLE:
        return new BMLLocalVariableExpression(readShort());
      case BMLAttributeTags.OLD_LOCAL_VARIABLE:
        return new BMLOldExpression(
            new BMLLocalVariableExpression(readShort()));
      case BMLAttributeTags.BOUND_VARIABLE:
        return new BMLBoundVariableExpression(readShort());
      default:
        notifyUnexpectedTag(tag);
        //@ unreachable
        return null;
    }
  }

  public BMLPredicate readPredicate() throws TroubleException {
    return new BMLPredicate(readExpression());
  }

  private BMLQuantifierExpression readQuantExpression(
      BMLQuantifierExpression.Operator operator) throws TroubleException {
    int bvCount = readByte();
    JType[] bvTypes = new JType[bvCount];
    for (int i = 0; i < bvTypes.length; i++) {
      readByte();
      bvTypes[i] = readType();
    }
    BMLExpression expr = readExpression();
    return new BMLQuantifierExpression(operator, bvTypes, expr);
  }

  private BMLFieldExpression readFieldExpression(boolean isGhostField)
      throws TroubleException {
    int cpIndex = classReader.getItem(readShort());
    String owner = classReader.readClass(cpIndex, buffer);
    cpIndex = classReader.getItem(classReader.readUnsignedShort(cpIndex + 2));
    String name = classReader.readUTF8(cpIndex, buffer);
    String desc = classReader.readUTF8(cpIndex + 2, buffer);

    return new BMLFieldExpression(
        TypeLoader.getClassType(owner),
        name,
        JType.fromDescriptor(desc),
        isGhostField);
  }

  private BMLExpression readFieldAccessExpression() throws TroubleException {
    // TODO[om]: Comment
    BMLExpression prefix = readExpression();
    boolean isOld = false;
    while (prefix instanceof BMLOldExpression) {
      prefix = ((BMLOldExpression) prefix).getExpression();
      isOld = true;
    }

    BMLExpression acc;
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.FIELD:
        acc = new BMLFieldAccessExpression(prefix, readFieldExpression(false));
        break;
      case BMLAttributeTags.OLD_FIELD:
        acc = new BMLFieldAccessExpression(prefix, readFieldExpression(false));
        isOld = true;
        break;
      case BMLAttributeTags.MODEL_FIELD:
        acc = new BMLFieldAccessExpression(prefix, readFieldExpression(true));
        break;
      case BMLAttributeTags.OLD_MODEL_FIELD:
        acc = new BMLFieldAccessExpression(prefix, readFieldExpression(true));
        isOld = true;
        break;
      case BMLAttributeTags.ARRAY_LENGTH:
        acc = new BMLArrayLengthExpression(prefix);
        break;
      default:
        notifyUnexpectedTag(tag);
        // unreachable
        return null;
    }

    return isOld ? new BMLOldExpression(acc) : acc;
  }

  private BMLExpression readArrayAccessExpression() throws TroubleException {
    // TODO[om]: Comment
    BMLExpression prefix = readExpression();
    boolean isOld = false;
    while (prefix instanceof BMLOldExpression) {
      prefix = ((BMLOldExpression) prefix).getExpression();
      isOld = true;
    }
    BMLExpression index = readExpression();
    BMLExpression acc = new BMLArrayAccessExpression(prefix, index);

    return isOld ? new BMLOldExpression(acc) : acc;
  }

  public BMLStoreRef readStoreRef() throws TroubleException {
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.MODIFIES_EVERYTHING:
        return BMLEverythingStoreRef.EVERYTHING;
      case BMLAttributeTags.MODIFIES_NOTHING:
        return BMLNothingStoreRef.NOTHING;
      case BMLAttributeTags.THIS:
        return BMLThisStoreRef.THIS;
      case BMLAttributeTags.MODIFIES_IDENT:
        return readIdentStoreRef();
      case BMLAttributeTags.LOCAL_VARIABLE:
        return new BMLLocalVariableStoreRef(readShort());
      case BMLAttributeTags.MODIFIES_DOT: {
        // TODO[om]: Check that field is of type BMLFieldStoreRef
        BMLFieldStoreRef field = (BMLFieldStoreRef) readStoreRef();
        BMLStoreRef prefix = readStoreRef();
        return new BMLFieldAccessStoreRef(prefix, field);
      }
      case BMLAttributeTags.MODIFIES_ARRAY:
        return readArrayStoreRef(readStoreRef());
      case BMLAttributeTags.FIELD_ACCESS:
        return readFieldAccessStoreRef();
      case BMLAttributeTags.ARRAY_ACCESS:
        return new BMLArrayElementStoreRef(readStoreRef(), readExpression());
      default:
        notifyUnexpectedTag(tag);
        // unreachable
        return null;
    }
  }

  private BMLStoreRef readIdentStoreRef() throws TroubleException {
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.FIELD:
        return readFieldStoreRef(false);
      case BMLAttributeTags.MODEL_FIELD:
        return readFieldStoreRef(true);
      case BMLAttributeTags.LOCAL_VARIABLE:
        return new BMLLocalVariableStoreRef(readShort());
      default:
        notifyUnexpectedTag(tag);
        // unreachable
        return null;
    }
  }

  private BMLStoreRef readFieldAccessStoreRef() throws TroubleException {
    BMLStoreRef prefix = readStoreRef();
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.FIELD:
        return new BMLFieldAccessStoreRef(prefix, readFieldStoreRef(false));
      case BMLAttributeTags.MODEL_FIELD:
        return new BMLFieldAccessStoreRef(prefix, readFieldStoreRef(true));
      default:
        notifyUnexpectedTag(tag);
        // unreachable
        return null;
    }
  }

  private BMLStoreRef readArrayStoreRef(BMLStoreRef prefix)
      throws TroubleException {
    int tag = readByte();
    switch (tag) {
      case BMLAttributeTags.MODIFIES_ARRAY_INDEX:
        return new BMLArrayElementStoreRef(prefix, readExpression());
      case BMLAttributeTags.MODIFIES_ARRAY_ALL:
        return new BMLArrayAllStoreRef(prefix);
      case BMLAttributeTags.MODIFIES_ARRAY_INTERVAL:
        return new BMLArrayRangeStoreRef(
            prefix,
            readExpression(),
            readExpression());
      default:
        notifyUnexpectedTag(tag);
        // unreachable
        return null;
    }
  }

  private BMLFieldStoreRef readFieldStoreRef(boolean isGhostField)
      throws TroubleException {
    int cpIndex = classReader.getItem(readShort());
    String owner = classReader.readClass(cpIndex, buffer);
    cpIndex = classReader.getItem(classReader.readUnsignedShort(cpIndex + 2));
    String name = classReader.readUTF8(cpIndex, buffer);
    String desc = classReader.readUTF8(cpIndex + 2, buffer);

    return new BMLFieldStoreRef(
        TypeLoader.getClassType(owner),
        name,
        JType.fromDescriptor(desc),
        isGhostField);
  }

  public String readString() throws TroubleException {
    // ASM's ClassReader.readUTF8(...) method below does NOT take the constant's
    // index into the constant pool directly as argument but rather the offset
    // of the classfile data where this index can be found. Hence, we use the
    // data offset as argument and simply skip the actual index.
    String string = classReader.readUTF8(current, buffer);
    readShort();
    return string;
  }

  public JType readType() throws TroubleException {
    // ASM's ClassReader.readUTF8(...) method below does NOT take the constant's
    // index into the constant pool directly as argument but rather the offset
    // of the classfile data where this index can be found. Hence, we use the
    // data offset as argument and simply skip the actual index.
    String descriptor = classReader.readUTF8(current, buffer);
    readShort();
    return JType.fromDescriptor(descriptor);
  }

  public int peekByte() throws TroubleException {
    if (current >= end) {
      throw new TroubleException(new TroubleMessage(
          B2BPLMessages.UNEXPECTED_END_OF_BML_ATTRIBUTE));
    }
    return classReader.b[current] & 0xFF;
  }

  public int readByte() throws TroubleException {
    if (current >= end) {
      throw new TroubleException(new TroubleMessage(
          B2BPLMessages.UNEXPECTED_END_OF_BML_ATTRIBUTE));
    }
    return classReader.b[current++] & 0xFF;
  }

  public int readShort() throws TroubleException {
    int b1 = readByte();
    int b2 = readByte();
    return (b1 << 8) | b2;
  }

  public int readInt() throws TroubleException {
    int s1 = readShort();
    int s2 = readShort();
    return (s1 << 16) | s2;
  }
}
