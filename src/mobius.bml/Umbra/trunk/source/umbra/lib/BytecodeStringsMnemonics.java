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
 * The container for all the byte code mnemonic strings. Except from a flat
 * list of mnemonics it contains arrays of mnemonics divided to different
 * classes which are represented in {@link umbra.instructions.ast} package.
 * It inherits the flat list of all instructions from
 * {@link BytecodeStringsGeneric}.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeStringsMnemonics extends BytecodeStringsGeneric {

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.ArithmeticInstruction} class.
   */
  public static final String[] ARITHMETIC_INS = new String[] {"dadd", "ddiv",
                                                              "dmul", "dneg",
                                                              "drem", "dsub",
                                                              "fadd", "fdiv",
                                                              "fmul", "fneg",
                                                              "frem", "fsub",
                                                              "iadd", "iand",
                                                              "imul", "idiv",
                                                              "ineg", "ior",
                                                              "isub", "irem",
                                                              "ishl",
                                                              "iushr", "ixor",
                                                              "lsub", "ladd",
                                                              "land", "ldiv",
                                                              "lmul", "lneg",
                                                              "lor", "lrem",
                                                              "lshl", "lshr",
                                                              "lushr", "lxor"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.IConstInstruction} class.
   */
  public static final String[] ICONST_INS = new String[] {"iconst_m1",
                                                          "iconst_0",
                                                          "iconst_1",
                                                          "iconst_2",
                                                          "iconst_3",
                                                          "iconst_4",
                                                          "iconst_5"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.LoadStoreConstInstruction} class.
   */
  public static final String[] LOAD_STORE_INS = new String[] {"aload_0",
                                                              "aload_1",
                                                              "aload_2",
                                                              "aload_3",
                                                              "astore_0",
                                                              "astore_1",
                                                              "astore_2",
                                                              "astore_3",
                                                              "dload_0",
                                                              "dload_1",
                                                              "dload_2",
                                                              "dload_3",
                                                              "dstore_0",
                                                              "dstore_1",
                                                              "dstore_2",
                                                              "dstore_3",
                                                              "fload_0",
                                                              "fload_1",
                                                              "fload_2",
                                                              "fload_3",
                                                              "fstore_0",
                                                              "fstore_1",
                                                              "fstore_2",
                                                              "fstore_3",
                                                              "iload_0",
                                                              "iload_1",
                                                              "iload_2",
                                                              "iload_3",
                                                              "istore_0",
                                                              "istore_1",
                                                              "istore_2",
                                                              "istore_3",
                                                              "lload_0",
                                                              "lload_1",
                                                              "lload_2",
                                                              "lload_3",
                                                              "lstore_0",
                                                              "lstore_1",
                                                              "lstore_2",
                                                              "lstore_3"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.LoadStoreArrayInstruction} class.
   */
  public static final String[] LOAD_STORE_ARRAY_INS = {"aaload",
                                                       "aastore",
                                                       "baload",
                                                       "bastore",
                                                       "caload",
                                                       "castore",
                                                       "daload",
                                                       "dastore",
                                                       "faload",
                                                       "fastore",
                                                       "iaload",
                                                       "iastore",
                                                       "laload",
                                                       "lastore",
                                                       "saload",
                                                       "sastore"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.SingleInstruction} class.
   */
  public static final String[] SINGLE_INS = new String[] {"aconst_null",
                                                          "arraylength",
                                                          "athrow", "lcmp",
                                                          "monitorenter",
                                                          "monitorexit",
                                                          "areturn", "dreturn",
                                                          "freturn", "ireturn",
                                                          "lreturn", "return",
                                                          "dup", "dup_x1",
                                                          "dup_x2", "dup2",
                                                          "dup2_x1", "dup2_x2",
                                                          "pop", "pop2",
                                                          "swap"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.PushInstruction} class.
   */
  public static final String[] PUSH_INS = new String[] {"bipush", "sipush"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.JumpInstruction} class.
   */
  public static final String[] JUMP_INS = new String[] {"goto", "goto_w",
                                                        "if_acmpeq",
                                                        "if_acmpne",
                                                        "if_icmpeq",
                                                        "if_icmpge",
                                                        "if_icmpgt",
                                                        "if_icmple",
                                                        "if_icmplt",
                                                        "if_icmpne", "ifeq",
                                                        "ifge", "ifgt", "ifle",
                                                        "iflt", "ifne",
                                                        "ifnonnull", "ifnull",
                                                        "jsr", "jsr_w",
                                                        "lookupswitch",
                                                        "tableswitch"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.ConversionInstruction} class.
   */
  public static final String[] CONV_INS = new String[] {"d2f",
                                                        "d2i",
                                                        "d2l",
                                                        "f2d",
                                                        "f2i",
                                                        "f2l",
                                                        "i2b",
                                                        "i2c",
                                                        "i2d",
                                                        "i2f",
                                                        "i2l",
                                                        "i2s",
                                                        "l2d",
                                                        "l2f",
                                                        "l2i"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.IincInstruction} class.
   */
  public static final String[] IINC_INS = new String[] {"iinc"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.StackInstruction} class.
   */
  public static final String[] STACK_INS = new String[] {"aload", "astore",
                                                         "dload", "dstore",
                                                         "fload", "fstore",
                                                         "iload", "istore",
                                                         "lload", "lstore"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.ArrayInstruction} class.
   */
  public static final String[] ARRAY_INS = new String[] {"newarray"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.NewInstruction} class.
   */
  public static final String[] NEW_INS = new String[] {"anewarray",
                                                       "checkcast",
                                                       "instanceof", "new"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.FieldInstruction} class.
   */
  public static final String[] FIELD_INS = new String[] {"getfield",
                                                         "getstatic",
                                                         "putfield",
                                                         "putstatic"};

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.InvokeInstruction} class.
   */
  public static final String[] INVOKE_INS = new String[] {"invokeinterface",
                                                          "invokespecial",
                                                          "invokestatic",
                                                          "invokevirtual"};

  /**
   * Contains the index to {@link #INVOKE_INS} of "invokeinterface".
   */
  public static final int INVOKEINTERFACE_NO = 0;

  /**
   * This constant contains an array with all the names of instructions handled
   * in {@link umbra.instructions.ast.LdcInstruction} class.
   */
  public static final String[] LDC_INS = new String[] {"ldc", "ldc_w",
                                                       "ldc2_w"};

  /**
   * This array contains instructions which are not handled by the Umbra
   * plugin.
   */
  public static final String[] UNCLASSIFIED_INS =
                                          new String[] {"breakpoint",
                                                        "multilinewarray",
                                                        "dcmpg",
                                                        "dcmpl",
                                                        "dconst",
                                                        "fcmpg",
                                                        "fcmpl",
                                                        "fconst",
                                                        "iconst",
                                                        "impdep1",
                                                        "impdep2",
                                                        "lconst",
                                                        "nop", "ret"};

  /**
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  protected BytecodeStringsMnemonics() {
  }
}
