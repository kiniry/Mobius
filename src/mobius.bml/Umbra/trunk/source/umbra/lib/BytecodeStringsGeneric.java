/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

/**
 * The class is a container for all byte code instructions and the sequences
 * that indicate the starts and ends of comments or BML annotation areas.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeStringsGeneric {

  /**
   * All the byte code mnemonics.
   */
  public static final String[] INSTRUCTIONS = new String[] {"aconst_null",
                                                            "dadd", "ddiv",
                                                            "dmul", "dneg",
                                                            "drem", "dsub",
                                                            "fadd", "fdiv",
                                                            "fmul", "fneg",
                                                            "frem", "fsub",
                                                            "iadd", "iand",
                                                            "idiv", "imul",
                                                            "ineg", "ior",
                                                            "irem", "isub",
                                                            "iushr", "ixor",
                                                            "ladd", "land",
                                                            "ldiv", "lmul",
                                                            "lneg", "lor",
                                                            "lrem", "lshl",
                                                            "lshr", "lsub",
                                                            "lushr", "lxor",
                                                            "aaload",
                                                            "aastore",
                                                            "baload", "bastore",
                                                            "caload", "castore",
                                                            "daload",
                                                            "dastore",
                                                            "faload",
                                                            "fastore",
                                                            "iaload",
                                                            "iastore",
                                                            "laload",
                                                            "lastore",
                                                            "saload",
                                                            "sastore",
                                                            "arraylength",
                                                            "athrow", "bipush",
                                                            "goto", "goto_w",
                                                            "if_acmpeq",
                                                            "if_acmpne",
                                                            "if_icmpeq",
                                                            "if_icmpge",
                                                            "if_icmpgt",
                                                            "if_icmple",
                                                            "if_icmplt",
                                                            "if_icmpne",
                                                            "ifeq", "ifge",
                                                            "ifgt", "ifle",
                                                            "iflt", "ifne",
                                                            "ifnonnull",
                                                            "ifnull", "jsr",
                                                            "jsr_w",
                                                            "lookupswitch",
                                                            "tableswitch",
                                                            "breakpoint",
                                                            "d2f", "d2i",
                                                            "d2l", "f2d",
                                                            "f2i", "f2l",
                                                            "i2b", "i2c",
                                                            "i2d", "i2f",
                                                            "i2l", "i2s",
                                                            "l2d", "l2f",
                                                            "l2i", "anewarray",
                                                            "checkcast",
                                                            "getfield",
                                                            "getstatic",
                                                            "putfield",
                                                            "putstatic",
                                                            "invokeinterface",
                                                            "invokespecial",
                                                            "invokestatic",
                                                            "invokevirtual",
                                                            "instanceof",
                                                            "ldc", "ldc_w",
                                                            "ldc2_w",
                                                            "multilinewarray",
                                                            "new", "dcmpg",
                                                            "dcmpl", "dconst",
                                                            "fcmpg", "fcmpl",
                                                            "fconst", "iconst",
                                                            "iconst_0",
                                                            "iconst_1",
                                                            "iconst_2",
                                                            "iconst_3",
                                                            "iconst_4",
                                                            "iconst_5",
                                                            "iconst_m1",
                                                            "impdep1",
                                                            "impdep2", "lcmp",
                                                            "lconst", "iinc",
                                                            "aload", "aload_0",
                                                            "aload_1",
                                                            "aload_2",
                                                            "aload_3",
                                                            "astore",
                                                            "astore_0",
                                                            "astore_1",
                                                            "astore_2",
                                                            "astore_3",
                                                            "dload", "dload_0",
                                                            "dload_1",
                                                            "dload_2",
                                                            "dload_3",
                                                            "dstore",
                                                            "dstore_0",
                                                            "dstore_1",
                                                            "dstore_2",
                                                            "dstore_3",
                                                            "fload", "fload_0",
                                                            "fload_1",
                                                            "fload_2",
                                                            "fload_3",
                                                            "fstore",
                                                            "fstore_0",
                                                            "fstore_1",
                                                            "fstore_2",
                                                            "fstore_3",
                                                            "iload", "iload_0",
                                                            "iload_1",
                                                            "iload_2",
                                                            "iload_3",
                                                            "istore",
                                                            "istore_0",
                                                            "istore_1",
                                                            "istore_2",
                                                            "istore_3",
                                                            "lload", "lload_0",
                                                            "lload_1",
                                                            "lload_2",
                                                            "lload_3",
                                                            "lstore",
                                                            "lstore_0",
                                                            "lstore_1",
                                                            "lstore_2",
                                                            "lstore_3",
                                                            "monitorenter",
                                                            "monitorexit",
                                                            "newarray", "nop",
                                                            "ret", "areturn",
                                                            "dreturn",
                                                            "freturn",
                                                            "ireturn",
                                                            "lreturn",
                                                            "return", "sipush",
                                                            "dup", "dup_x1",
                                                            "dup_x2", "dup2",
                                                            "dup2_x1",
                                                            "dup2_x2", "pop",
                                                            "pop2", "swap"};

  /**
   * This string contains the multi-line comment start.
   */
  public static final String COMMENT_LINE_START = "/*";

  /**
   * This string contains the multi-line comment end.
   */
  public static final String COMMENT_LINE_END = "*/";

  /**
   * The string which starts a single line comment in a byte code file.
   */
  public static final String SINGLE_LINE_COMMENT_MARK = "//";

  /**
   * The length of the single line comment marker.
   */
  public static final int SINGLE_LINE_COMMENT_MARK_LEN =
                                              SINGLE_LINE_COMMENT_MARK.length();
  /*@ static invariant SINGLE_LINE_COMMENT_MARK_LEN ==
    @                  SINGLE_LINE_COMMENT_MARK.length();
    @*/


  /**
   * This string contains the BML annotation comment start.
   */
  public static final String ANNOT_START = "/*@";

  /**
   * This string contains the BML annotation comment end i.e. @*\/.
   */
  public static final String ANNOT_END = "@*/";

  /**
   * This string contains the BML annotation comment end.
   */
  public static final String ANNOT_END_SIMPLE = "*/";

  /**
   * This string contains the BML annotation comment end.
   */
  public static final String ANNOT_ONELINE_START = "//@";

  /**
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  protected BytecodeStringsGeneric() {
  }
}
