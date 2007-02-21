package b2bpl.bytecode;


public interface Opcodes {

  int NOP = 0;

  int ACONST_NULL = 1;

  int ICONST_M1 = 2;

  int ICONST_0 = 3;

  int ICONST_1 = 4;

  int ICONST_2 = 5;

  int ICONST_3 = 6;

  int ICONST_4 = 7;

  int ICONST_5 = 8;

  int LCONST_0 = 9;

  int LCONST_1 = 10;

  int FCONST_0 = 11;

  int FCONST_1 = 12;

  int FCONST_2 = 13;

  int DCONST_0 = 14;

  int DCONST_1 = 15;

  int BIPUSH = 16;

  int SIPUSH = 17;

  int LDC = 18;

  int LDC_W = 19;

  int LDC2_W = 20;

  int ILOAD = 21;

  int LLOAD = 22;

  int FLOAD = 23;

  int DLOAD = 24;

  int ALOAD = 25;

  int ILOAD_0 = 26;

  int ILOAD_1 = 27;

  int ILOAD_2 = 28;

  int ILOAD_3 = 29;

  int LLOAD_0 = 30;

  int LLOAD_1 = 31;

  int LLOAD_2 = 32;

  int LLOAD_3 = 33;

  int FLOAD_0 = 34;

  int FLOAD_1 = 35;

  int FLOAD_2 = 36;

  int FLOAD_3 = 37;

  int DLOAD_0 = 38;

  int DLOAD_1 = 39;

  int DLOAD_2 = 40;

  int DLOAD_3 = 41;

  int ALOAD_0 = 42;

  int ALOAD_1 = 43;

  int ALOAD_2 = 44;

  int ALOAD_3 = 45;

  int IALOAD = 46;

  int LALOAD = 47;

  int FALOAD = 48;

  int DALOAD = 49;

  int AALOAD = 50;

  int BALOAD = 51;

  int CALOAD = 52;

  int SALOAD = 53;

  int ISTORE = 54;

  int LSTORE = 55;

  int FSTORE = 56;

  int DSTORE = 57;

  int ASTORE = 58;

  int ISTORE_0 = 59;

  int ISTORE_1 = 60;

  int ISTORE_2 = 61;

  int ISTORE_3 = 62;

  int LSTORE_0 = 63;

  int LSTORE_1 = 64;

  int LSTORE_2 = 65;

  int LSTORE_3 = 66;

  int FSTORE_0 = 67;

  int FSTORE_1 = 68;

  int FSTORE_2 = 69;

  int FSTORE_3 = 70;

  int DSTORE_0 = 71;

  int DSTORE_1 = 72;

  int DSTORE_2 = 73;

  int DSTORE_3 = 74;

  int ASTORE_0 = 75;

  int ASTORE_1 = 76;

  int ASTORE_2 = 77;

  int ASTORE_3 = 78;

  int IASTORE = 79;

  int LASTORE = 80;

  int FASTORE = 81;

  int DASTORE = 82;

  int AASTORE = 83;

  int BASTORE = 84;

  int CASTORE = 85;

  int SASTORE = 86;

  int POP = 87;

  int POP2 = 88;

  int DUP = 89;

  int DUP_X1 = 90;

  int DUP_X2 = 91;

  int DUP2 = 92;

  int DUP2_X1 = 93;

  int DUP2_X2 = 94;

  int SWAP = 95;

  int IADD = 96;

  int LADD = 97;

  int FADD = 98;

  int DADD = 99;

  int ISUB = 100;

  int LSUB = 101;

  int FSUB = 102;

  int DSUB = 103;

  int IMUL = 104;

  int LMUL = 105;

  int FMUL = 106;

  int DMUL = 107;

  int IDIV = 108;

  int LDIV = 109;

  int FDIV = 110;

  int DDIV = 111;

  int IREM = 112;

  int LREM = 113;

  int FREM = 114;

  int DREM = 115;

  int INEG = 116;

  int LNEG = 117;

  int FNEG = 118;

  int DNEG = 119;

  int ISHL = 120;

  int LSHL = 121;

  int ISHR = 122;

  int LSHR = 123;

  int IUSHR = 124;

  int LUSHR = 125;

  int IAND = 126;

  int LAND = 127;

  int IOR = 128;

  int LOR = 129;

  int IXOR = 130;

  int LXOR = 131;

  int IINC = 132;

  int I2L = 133;

  int I2F = 134;

  int I2D = 135;

  int L2I = 136;

  int L2F = 137;

  int L2D = 138;

  int F2I = 139;

  int F2L = 140;

  int F2D = 141;

  int D2I = 142;

  int D2L = 143;

  int D2F = 144;

  int I2B = 145;

  int I2C = 146;

  int I2S = 147;

  int LCMP = 148;

  int FCMPL = 149;

  int FCMPG = 150;

  int DCMPL = 151;

  int DCMPG = 152;

  int IFEQ = 153;

  int IFNE = 154;

  int IFLT = 155;

  int IFGE = 156;

  int IFGT = 157;

  int IFLE = 158;

  int IF_ICMPEQ = 159;

  int IF_ICMPNE = 160;

  int IF_ICMPLT = 161;

  int IF_ICMPGE = 162;

  int IF_ICMPGT = 163;

  int IF_ICMPLE = 164;

  int IF_ACMPEQ = 165;

  int IF_ACMPNE = 166;

  int GOTO = 167;

  int JSR = 168;

  int RET = 169;

  int TABLESWITCH = 170;

  int LOOKUPSWITCH = 171;

  int IRETURN = 172;

  int LRETURN = 173;

  int FRETURN = 174;

  int DRETURN = 175;

  int ARETURN = 176;

  int RETURN = 177;

  int GETSTATIC = 178;

  int PUTSTATIC = 179;

  int GETFIELD = 180;

  int PUTFIELD = 181;

  int INVOKEVIRTUAL = 182;

  int INVOKESPECIAL = 183;

  int INVOKESTATIC = 184;

  int INVOKEINTERFACE = 185;

  int NEW = 187;

  int NEWARRAY = 188;

  int ANEWARRAY = 189;

  int ARRAYLENGTH = 190;

  int ATHROW = 191;

  int CHECKCAST = 192;

  int INSTANCEOF = 193;

  int MONITORENTER = 194;

  int MONITOREXIT = 195;

  int WIDE = 196;

  int MULTIANEWARRAY = 197;

  int IFNULL = 198;

  int IFNONNULL = 199;

  int GOTO_W = 200;

  int JSR_W = 201;


  String[] NAMES = {
      "NOP", "ACONST_NULL", "ICONST_M1", "ICONST_0", "ICONST_1",
      "ICONST_2", "ICONST_3", "ICONST_4", "ICONST_5", "LCONST_0", "LCONST_1",
      "FCONST_0", "FCONST_1", "FCONST_2", "DCONST_0", "DCONST_1", "BIPUSH",
      "SIPUSH", "LDC", "LDC_W", "LDC2_W", "ILOAD", "LLOAD", "FLOAD", "DLOAD",
      "ALOAD", "ILOAD_0", "ILOAD_1", "ILOAD_2", "ILOAD_3", "LLOAD_0",
      "LLOAD_1", "LLOAD_2", "LLOAD_3", "FLOAD_0", "FLOAD_1", "FLOAD_2",
      "FLOAD_3", "DLOAD_0", "DLOAD_1", "DLOAD_2", "DLOAD_3", "ALOAD_0",
      "ALOAD_1", "ALOAD_2", "ALOAD_3", "IALOAD", "LALOAD", "FALOAD", "DALOAD",
      "AALOAD", "BALOAD", "CALOAD", "SALOAD", "ISTORE", "LSTORE", "FSTORE",
      "DSTORE", "ASTORE", "ISTORE_0", "ISTORE_1", "ISTORE_2", "ISTORE_3",
      "LSTORE_0", "LSTORE_1", "LSTORE_2", "LSTORE_3", "FSTORE_0", "FSTORE_1",
      "FSTORE_2", "FSTORE_3", "DSTORE_0", "DSTORE_1", "DSTORE_2", "DSTORE_3",
      "ASTORE_0", "ASTORE_1", "ASTORE_2", "ASTORE_3", "IASTORE", "LASTORE",
      "FASTORE", "DASTORE", "AASTORE", "BASTORE", "CASTORE", "SASTORE", "POP",
      "POP2", "DUP", "DUP_X1", "DUP_X2", "DUP2", "DUP2_X1", "DUP2_X2", "SWAP",
      "IADD", "LADD", "FADD", "DADD", "ISUB", "LSUB", "FSUB", "DSUB", "IMUL",
      "LMUL", "FMUL", "DMUL", "IDIV", "LDIV", "FDIV", "DDIV", "IREM", "LREM",
      "FREM", "DREM", "INEG", "LNEG", "FNEG", "DNEG", "ISHL", "LSHL", "ISHR",
      "LSHR", "IUSHR", "LUSHR", "IAND", "LAND", "IOR", "LOR", "IXOR", "LXOR",
      "IINC", "I2L", "I2F", "I2D", "L2I", "L2F", "L2D", "F2I", "F2L", "F2D",
      "D2I", "D2L", "D2F", "I2B", "I2C", "I2S", "LCMP", "FCMPL", "FCMPG",
      "DCMPL", "DCMPG", "IFEQ", "IFNE", "IFLT", "IFGE", "IFGT", "IFLE",
      "IF_ICMPEQ", "IF_ICMPNE", "IF_ICMPLT", "IF_ICMPGE", "IF_ICMPGT",
      "IF_ICMPLE", "IF_ACMPEQ", "IF_ACMPNE", "GOTO", "JSR", "RET",
      "TABLESWITCH", "LOOKUPSWITCH", "IRETURN", "LRETURN", "FRETURN",
      "DRETURN", "ARETURN", "RETURN", "GETSTATIC", "PUTSTATIC", "GETFIELD",
      "PUTFIELD", "INVOKEVIRTUAL", "INVOKESPECIAL", "INVOKESTATIC",
      "INVOKEINTERFACE", "<UNDEFINED>", "NEW", "NEWARRAY", "ANEWARRAY",
      "ARRAYLENGTH", "ATHROW", "CHECKCAST", "INSTANCEOF", "MONITORENTER",
      "MONITOREXIT", "WIDE", "MULTIANEWARRAY", "IFNULL", "IFNONNULL", "GOTO_W",
      "JSR_W"
  };

  // types for NEWARRAY
  int T_BOOLEAN = 4;

  int T_CHAR = 5;

  int T_FLOAT = 6;

  int T_DOUBLE = 7;

  int T_BYTE = 8;

  int T_SHORT = 9;

  int T_INT = 10;

  int T_LONG = 11;
}
