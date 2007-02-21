package b2bpl.translation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

import b2bpl.Project;
import b2bpl.bpl.ast.BPLAxiom;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLConstantDeclaration;
import b2bpl.bpl.ast.BPLDeclaration;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLFunction;
import b2bpl.bpl.ast.BPLFunctionParameter;
import b2bpl.bpl.ast.BPLIntLiteral;
import b2bpl.bpl.ast.BPLProgram;
import b2bpl.bpl.ast.BPLType;
import b2bpl.bpl.ast.BPLTypeDeclaration;
import b2bpl.bpl.ast.BPLTypeName;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JBaseType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.bml.ast.BMLExpression;


/**
 * The main entry point to the translation of a set of bytecode classes to a
 * BoogiePL program.
 *
 * <p>
 * Some aspects of the translation process can be configured by passing an
 * appropriate {@link Project} instance containing the desired translation
 * settings upon creating the <code>Translator</code>. In particular, the
 * following aspects of the translation can be configured:
 * <ul>
 *   <li>
 *     The verification methodology for object invariants
 *     (see {@link Project#isThisInvariantsOnly()}).
 *   </li>
 *   <li>
 *     Whether to explicitly model runtime exceptions instead of ruling them
 *     out by verification conditions
 *     (see {@link Project#isModelRuntimeExceptions()}).
 *   </li>
 *   <li>
 *     The maximal magnitude of integer constants to represent explicitly in
 *     the BoogiePL program (see {@link Project#getMaxIntConstant()}).
 *   </li>
 * </ul>
 * </p>
 *
 * <p>
 * The <code>Translator</code> is <i>immediately</i> responsible for generating
 * the following parts of the resulting BoogiePL program:
 * <ul>
 *   <li>
 *     The core part of the background theory which is the same for every
 *     translation. This mainly includes the heap and core type system
 *     axiomatization (array subtyping, value type ranges, ...).
 *   </li>
 *   <li>
 *     The global axiomatization which depends on the concrete bytecode classes
 *     being translated. As an example, every type referenced in a class will
 *     trigger the declaration of a constant representing the type as well as
 *     the generation of a set of axioms defining the type's supertype
 *     hierarchy as well as other properties such as whether the type is final
 *     or not. References to fields and special constants (such as strings)
 *     also lead to a set of global declarations being generated.
 *   </li>
 * </ul>
 * The following parts of a bytecode class are not directly translated by this
 * class but their translation is instead <i>delegated</i> to other classes:
 * <ul>
 *   <li>
 *     The actual BML specifications which appear in the global section of the
 *     resulting BoogiePL program (in particular type specifications such as
 *     invariants) are translated by a {@link SpecificationTranslator}.
 *   </li>
 *   <li>
 *     The individual methods are translated by a {@link MethodTranslator}
 *     which maps every bytecode method to a single BoogiePL procedure.
 *   </li>
 * </ul>
 * Since BML specifications and bytecode methods may contain type references
 * and other references which may require global axioms to be generated, the
 * <code>Translator</code> passes a {@link TranslationContext} to every
 * <code>SpecificationTranslator</code> and <code>MethodTranslator</code> which
 * should be used to translate those references.
 * </p>
 *
 * @see Project#isThisInvariantsOnly()
 * @see Project#isModelRuntimeExceptions()
 * @see Project#getMaxIntConstant()
 * @see SpecificationTranslator
 * @see MethodTranslator
 * @see TranslationContext
 *
 * @author Ovidio Mallo
 */
public class Translator extends CodeGenerator implements TranslationConstants {

  /** The project containing the settings of the translation. */
  private final Project project;

  /**
   * The <code>TranslationContext</code> responsible for resolving special
   * references (type/field/string/... references) encountered in the bytecode
   * classes being translated. This context is passed to all
   * <code>SpecificationTranslator</code>s and <code>MethodTranslator</code>s
   * to which part of the translation is delegated.
   */
  private Context context;

  /**
   * The set of declarations generated during the translation of the given
   * bytecode classes. These make up the resulting BoogiePL program.
   */
  private List<BPLDeclaration> declarations;

  /** The set of value types explicitly supported by the translation. */
  private static final JBaseType[] valueTypes = new JBaseType[] {
    JBaseType.INT,
    JBaseType.SHORT,
    JBaseType.BYTE,
    JBaseType.BOOLEAN,
    JBaseType.CHAR
  };

  /**
   * Creates a new translator which is configured by the given
   * <code>project</code>.
   * Once a translator has been created, it can be used to translate different
   * bytecode classes under the same configuration (given by the here provided
   * <code>project</code>).
   *
   * @param project  The project containing the configurations of the
   *                 translation.
   *
   * @see #translate(JClassType[])
   */
  public Translator(Project project) {
    this.project = project;
  }

  /**
   * Performs the actual translation of the given bytecode classes and returns
   * a BoogiePL program representing it.
   *
   * @param types  The bytecode classes to be translated.
   * @return       The BoogiePL program resulting from the translation of
   *               the given bytecode classes.
   */
  public BPLProgram translate(JClassType... types) {
    context = new Context();
    declarations = new ArrayList<BPLDeclaration>();
    MethodTranslator methodTranslator = new MethodTranslator(project);
    generateTheory();
    for (JClassType type : types) {
      for (BCMethod method : type.getMethods()) {
        if (!method.isAbstract() && !method.isNative()) {
          declarations.add(methodTranslator.translate(context, method));
        }
      }
    }
    flushPendingTheory();
    return new BPLProgram(
        declarations.toArray(new BPLDeclaration[declarations.size()]));
  }

  /**
   * Convenience method for adding the given <code>axiom</code> to the global
   * declarations of the BoogiePL program being generated.
   *
   * @param axiom  The axiom to add to the BoogiePL program.
   */
  private void addAxiom(BPLExpression axiom) {
    declarations.add(new BPLAxiom(axiom));
  }

  /**
   * Convenience method for adding a set of <code>constants</code> to the global
   * declarations of the BoogiePL program being generated.
   *
   * @param constants  The constants to add to the BoogiePL program.
   */
  private void addConstants(BPLVariable... constants) {
    declarations.add(new BPLConstantDeclaration(constants));
  }

  private void addFunction(String name, BPLType inType, BPLType outType) {
    addFunction(name, new BPLType[] { inType }, outType);
  }

  private void addFunction(
      String name,
      BPLType inType1,
      BPLType inType2,
      BPLType outType) {
    addFunction(name, new BPLType[] { inType1, inType2 }, outType);
  }

  private void addFunction(
      String name,
      BPLType inType1,
      BPLType inType2,
      BPLType inType3,
      BPLType outType) {
    addFunction(name, new BPLType[] { inType1, inType2, inType3 }, outType);
  }

  private void addFunction(
      String name,
      BPLType[] inTypes,
      BPLType outType) {
    BPLFunctionParameter[] inParameters =
      new BPLFunctionParameter[inTypes.length];
    for (int i = 0; i < inParameters.length; i++) {
      inParameters[i] = new BPLFunctionParameter(inTypes[i]);
    }
    addFunction(name, inParameters, new BPLFunctionParameter(outType));
  }

  private void addFunction(
      String name,
      BPLFunctionParameter[] inParameters,
      BPLFunctionParameter outParameter) {
    declarations.add(new BPLFunction(name, inParameters, outParameter));
  }

  /**
   * Convenience method for adding a set of user-defined types with the given
   * <code>names</code> to the global declarations of the BoogiePL program being
   * generated.
   *
   * @param names  The names of the user-defined types to add to the BoogiePL
   *               program.
   */
  private void addTypes(String... names) {
    declarations.add(new BPLTypeDeclaration(names));
  }

  /**
   * Returns the name of a BoogiePL constant to be used to reference the given
   * value <code>type</code>.
   *
   * @param type  The value type for which to build the constant name.
   * @return      The name of the constant representing the given value
   *              <code>type</code>.
   */
  private String getValueTypeName(JBaseType type) {
    return VALUE_TYPE_PREFIX + type.getName();
  }

  /**
   * Returns the name of a BoogiePL constant to be used to reference the given
   * class <code>type</code>.
   *
   * @param type  The class type for which to build the constant name.
   * @return      The name of the constant representing the given class
   *              <code>type</code>.
   */
  private String getClassTypeName(JClassType type) {
    return GLOBAL_VAR_PREFIX + type.getName();
  }

  /**
   * Returns the smallest integer constant in the value range of the given
   * <code>type</code>.
   *
   * @return  The smallest integer constant of the given <code>type</code>.
   */
  private int getMinValue(JBaseType type) {
    if (type.equals(JBaseType.INT)) {
      return Integer.MIN_VALUE;
    } else if (type.equals(JBaseType.SHORT)) {
      return Short.MIN_VALUE;
    } else if (type.equals(JBaseType.BYTE)) {
      return Byte.MIN_VALUE;
    } else if (type.equals(JBaseType.BOOLEAN)) {
      return 0;
    } else if (type.equals(JBaseType.CHAR)) {
      return Character.MIN_VALUE;
    }
    throw new IllegalArgumentException("internal error");
  }

  /**
   * Returns the greatest integer constant in the value range of the given
   * <code>type</code>.
   *
   * @return  The greatest integer constant of the given <code>type</code>.
   */
  private int getMaxValue(JBaseType type) {
    if (type.equals(JBaseType.INT)) {
      return Integer.MAX_VALUE;
    } else if (type.equals(JBaseType.SHORT)) {
      return Short.MAX_VALUE;
    } else if (type.equals(JBaseType.BYTE)) {
      return Byte.MAX_VALUE;
    } else if (type.equals(JBaseType.BOOLEAN)) {
      return 1;
    } else if (type.equals(JBaseType.CHAR)) {
      return Character.MAX_VALUE;
    }
    throw new IllegalArgumentException("internal error");
  }

  /**
   * Returns the name of a BoogiePL constant representing the given
   * <code>literal</code>.
   * This method is used for integer values which are abstractly represented
   * by constants since their magnitude is considered to be too large to be
   * handled by theorem provers.
   *
   * @param literal  The value for which to build the constant name.
   * @return         The name of the constant representing the given
   *                 <code>literal</code>.
   */
  private String getSymbolicIntLiteralName(int literal) {
    return INT_LITERAL_PREFIX + String.valueOf(literal).replace('-', 'm');
  }

  /**
   * Convenience method for translating a type reference.
   *
   * @param type  The type reference to translate.
   * @return      A BoogiePL expression representing the given type reference.
   */
  private BPLExpression typeRef(JType type) {
    return context.translateTypeReference(type);
  }

  /**
   * Convenience method for translating an integer constant.
   *
   * @param literal  The integer constant to translate.
   * @return         A BoogiePL expression representing the given integer
   *                 constant.
   */
  private BPLExpression intLiteral(int literal) {
    return context.translateIntLiteral(literal);
  }

  /**
   * Generates the core part of the background theory which is the same for
   * every translation.
   */
  private void generateTheory() {
    axiomatizeHeap();
    axiomatizeHelperFunctions();
    axiomatizeTypeSystem();
    axiomatizeArithmetic();
    axiomatizeBitwiseInstructions();
  }

  /**
   * Axiomatizes some properties of arithmetic operations in order to later
   * support the theorem prover in verifying programs containing arithmetic
   * expressions.
   */
  private void axiomatizeArithmetic() {
    String i = quantVarName("i");
    String j = quantVarName("j");
    BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
    BPLVariable jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        isEqual(
            modulo(var(i), var(j)),
            sub(var(i), multiply(divide(var(i), var(j)), var(j)))),
        trigger(modulo(var(i), var(j))),
        trigger(divide(var(i), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                less(intLiteral(0), var(j))),
            logicalAnd(
                lessEqual(intLiteral(0), modulo(var(i), var(j))),
                less(modulo(var(i), var(j)), var(j)))),
        trigger(modulo(var(i), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                less(var(j), intLiteral(0))),
            logicalAnd(
                lessEqual(intLiteral(0), modulo(var(i), var(j))),
                less(modulo(var(i), var(j)), sub(intLiteral(0), var(j))))),
        trigger(modulo(var(i), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(var(i), intLiteral(0)),
                less(intLiteral(0), var(j))),
            logicalAnd(
                less(sub(intLiteral(0), var(j)), modulo(var(i), var(j))),
                lessEqual(modulo(var(i), var(j)), intLiteral(0)))),
        trigger(modulo(var(i), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(var(i), intLiteral(0)),
                less(var(j), intLiteral(0))),
            logicalAnd(
                less(var(j), modulo(var(i), var(j))),
                lessEqual(modulo(var(i), var(j)), intLiteral(0)))),
        trigger(modulo(var(i), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            isEqual(
                modulo(add(var(i), var(j)), var(j)),
                modulo(var(i), var(j)))),
        trigger(modulo(add(var(i), var(j)), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            isEqual(
                modulo(add(var(j), var(i)), var(j)),
                modulo(var(i), var(j)))),
        trigger(modulo(add(var(j), var(i)), var(j)))));

    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), sub(var(i), var(j))),
                lessEqual(intLiteral(0), var(j))),
            isEqual(
                modulo(sub(var(i), var(j)), var(j)),
                modulo(var(i), var(j)))),
        trigger(modulo(sub(var(i), var(j)), var(j)))));

    String a = quantVarName("a");
    String b = quantVarName("b");
    String d = quantVarName("d");
    BPLVariable aVar = new BPLVariable(a, BPLBuiltInType.INT);
    BPLVariable bVar = new BPLVariable(b, BPLBuiltInType.INT);
    BPLVariable dVar = new BPLVariable(d, BPLBuiltInType.INT);
    addAxiom(forall(
        aVar, bVar, dVar,
        implies(
            logicalAnd(
                logicalAnd(
                    lessEqual(intLiteral(2), var(d)),
                    isEqual(modulo(var(a), var(d)), modulo(var(b), var(d)))),
                less(var(a), var(b))),
            lessEqual(add(var(a), var(d)), var(b))),
        trigger(modulo(var(a), var(d)), modulo(var(b), var(d)))));
  }

  /**
   * Axiomatizes the semantics of bitwise arithmetic operations which are not
   * directly supported by BoogiePL.
   */
  private void axiomatizeBitwiseInstructions() {
    addFunction(
        SHL_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);
    addFunction(
        SHR_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);
    addFunction(
        USHR_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);
    addFunction(
        AND_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);
    addFunction(
        OR_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);
    addFunction(
        XOR_FUNC,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT,
        BPLBuiltInType.INT);

    // shift left
    String i = quantVarName("i");
    BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar,
        isEqual(bitShl(var(i), intLiteral(0)), var(i)),
        trigger(bitShl(var(i), intLiteral(0)))));
    String j = quantVarName("j");
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    BPLVariable jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            less(intLiteral(0), var(j)),
            isEqual(
                bitShl(var(i), var(j)),
                multiply(
                    bitShl(var(i), sub(var(j), intLiteral(1))),
                    intLiteral(2))))));

    // shift right
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar,
        isEqual(bitShr(var(i), intLiteral(0)), var(i)),
        trigger(bitShr(var(i), intLiteral(0)))));
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            less(intLiteral(0), var(j)),
            isEqual(
                bitShr(var(i), var(j)),
                divide(
                    bitShr(var(i), sub(var(j), intLiteral(1))),
                    intLiteral(2))))));

    // unsigned shift right
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            lessEqual(intLiteral(0), var(i)),
            isEqual(bitUShr(var(i), var(j)), bitShr(var(i), var(j)))),
        trigger(bitUShr(var(i), var(j)))));
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            less(intLiteral(0), var(j)),
            lessEqual(intLiteral(0), bitUShr(var(i), var(j)))),
        trigger(bitUShr(var(i), var(j)))));

    // bitwise and
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        isEquiv(
            logicalOr(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            lessEqual(intLiteral(0), bitAnd(var(i), var(j)))),
        trigger(bitAnd(var(i), var(j)))));
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            isEqual(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            logicalAnd(
                lessEqual(bitAnd(var(i), var(j)), var(i)),
                lessEqual(bitAnd(var(i), var(j)), var(j)))),
        trigger(bitAnd(var(i), var(j)))));

    // bitwise or
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        isEquiv(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            lessEqual(intLiteral(0), bitOr(var(i), var(j)))),
        trigger(bitOr(var(i), var(j)))));
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        implies(
            logicalAnd(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            lessEqual(bitOr(var(i), var(j)), add(var(i), var(j)))),
        trigger(bitOr(var(i), var(j)))));

    // bitwise xor
    iVar = new BPLVariable(i, BPLBuiltInType.INT);
    jVar = new BPLVariable(j, BPLBuiltInType.INT);
    addAxiom(forall(
        iVar, jVar,
        isEquiv(
            isEqual(
                lessEqual(intLiteral(0), var(i)),
                lessEqual(intLiteral(0), var(j))),
            lessEqual(intLiteral(0), bitXor(var(i), var(j)))),
        trigger(bitXor(var(i), var(j)))));
  }

  /**
   * Adds the heap axiomatization to the background theory.
   */
  private void axiomatizeHeap() {
    //
    // Müller/Poetzsch Heffter BoogiePL store axiomatization
    //
    addTypes(HEAP_TYPE);

    //
    // Types
    //
    addFunction(IS_CLASS_TYPE_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.BOOL);
    addFunction(IS_VALUE_TYPE_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.BOOL);

    {
      // primitive types
      for (JBaseType valueType : valueTypes) {
        addConstants(new BPLVariable(
            getValueTypeName(valueType),
            BPLBuiltInType.NAME));
      }

      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      BPLExpression[] vtExprs = new BPLExpression[valueTypes.length];
      for (int i = 0; i < valueTypes.length; i++) {
        vtExprs[i] = isEqual(var(t), typeRef(valueTypes[i]));
      }
      addAxiom(forall(tVar, isEquiv(isValueType(var(t)), logicalOr(vtExprs))));
    }

    {
      addFunction(
          IS_IN_RANGE_FUNC,
          BPLBuiltInType.INT,
          BPLBuiltInType.NAME,
          BPLBuiltInType.BOOL);

      for (JBaseType valueType : valueTypes) {
        String i = quantVarName("i");
        BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
        addAxiom(forall(
            iVar,
            isEquiv(
                isInRange(var(i), typeRef(valueType)),
                logicalAnd(
                    lessEqual(intLiteral(getMinValue(valueType)), var(i)),
                    lessEqual(var(i), intLiteral(getMaxValue(valueType)))))));
      }

      String i = quantVarName("i");
      String t = quantVarName("t");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          iVar, tVar,
          isEquiv(
              isSubtype(typ(ival(var(i))), var(t)),
              isInRange(var(i), var(t)))));
    }

    {
      // casting of value types
      addFunction(
          ICAST_FUNC,
          BPLBuiltInType.INT,
          BPLBuiltInType.NAME,
          BPLBuiltInType.INT);

      // a cast value is in the value range of the target type
      String i = quantVarName("i");
      String t = quantVarName("t");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          iVar, tVar,
          isInRange(icast(var(i), var(t)), var(t))));

      // values which already are in the target value range are not affected
      // by a cast
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          iVar, tVar,
          implies(
              isInRange(var(i), var(t)),
              isEqual(icast(var(i), var(t)), var(i)))));
    }

    {
      // array types
      addFunction(ARRAY_TYPE_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.NAME);

      addFunction(ELEMENT_TYPE_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.NAME);
      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(tVar, isEqual(elementType(arrayType(var(t))), var(t))));
    }

    //
    // Values (objects, primitive values, arrays)
    //
    addTypes(VALUE_TYPE);

    {
      // integer values
      addFunction(IVAL_FUNC, BPLBuiltInType.INT, new BPLTypeName(VALUE_TYPE));
      String i = quantVarName("i");
      String j = quantVarName("j");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable jVar = new BPLVariable(j, BPLBuiltInType.INT);
      addAxiom(forall(
          iVar, jVar,
          isEquiv(
              isEqual(ival(var(i)), ival(var(j))),
              isEqual(var(i), var(j)))));
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(vVar, isEqual(ival(toint(var(v))), var(v))));

      addFunction(TOINT_FUNC, new BPLTypeName(VALUE_TYPE), BPLBuiltInType.INT);
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(iVar, isEqual(toint(ival(var(i))), var(i))));
    }

    {
      // reference values
      addFunction(RVAL_FUNC, BPLBuiltInType.REF, new BPLTypeName(VALUE_TYPE));
      String o1 = quantVarName("o1");
      String o2 = quantVarName("o2");
      BPLVariable o1Var = new BPLVariable(o1, BPLBuiltInType.REF);
      BPLVariable o2Var = new BPLVariable(o2, BPLBuiltInType.REF);
      addAxiom(forall(
          o1Var, o2Var,
          isEquiv(
              isEqual(rval(var(o1)), rval(var(o2))),
              isEqual(var(o1), var(o2)))));
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(vVar, isEqual(rval(toref(var(v))), var(v))));

      addFunction(TOREF_FUNC, new BPLTypeName(VALUE_TYPE), BPLBuiltInType.REF);
      String o = quantVarName("o");
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      addAxiom(forall(oVar, isEqual(toref(rval(var(o))), var(o))));
    }

    {
      // integer and reference values
      String i = quantVarName("i");
      String o = quantVarName("o");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      addAxiom(forall(iVar, oVar, notEqual(ival(var(i)), rval(var(o)))));
    }

    {
      // type of a value
      addFunction(TYP_FUNC, new BPLTypeName(VALUE_TYPE),  BPLBuiltInType.NAME);
      String i = quantVarName("i");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(iVar, isValueType(typ(ival(var(i))))));
    }

    {
      // uninitialized (default) value
      addFunction(INIT_FUNC, BPLBuiltInType.NAME, new BPLTypeName(VALUE_TYPE));

      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          tVar,
          implies(
              isValueType(var(t)),
              isEqual(initVal(var(t)), ival(intLiteral(0))))));

      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          tVar,
          implies(
              isClassType(var(t)),
              isEqual(initVal(var(t)), rval(nullLiteral())))));

      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          tVar,
          isEqual(
              initVal(arrayType(elementType(var(t)))),
              rval(nullLiteral()))));
    }

    {
      // static values
      addFunction(
          STATIC_FUNC,
          new BPLTypeName(VALUE_TYPE),
          BPLBuiltInType.BOOL);
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          vVar,
          isEquiv(
              isStatic(var(v)),
              logicalOr(
                  isValueType(typ(var(v))),
                  isEqual(var(v), rval(nullLiteral()))))));
    }

    {
      // array length
      addFunction(
          ARRAY_LENGTH_FUNC,
          new BPLTypeName(VALUE_TYPE),
          BPLBuiltInType.INT);
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(vVar, lessEqual(intLiteral(0), arrayLength((var(v))))));
    }

    //
    // Locations (fields and array elements)
    //
    addTypes(LOCATION_TYPE);

    {
      // An instance field (use typeObject for static fields)
      addFunction(
          FIELD_LOC_FUNC,
          BPLBuiltInType.REF,
          BPLBuiltInType.NAME,
          new BPLTypeName(LOCATION_TYPE));
      String o1 = quantVarName("o1");
      String f1 = quantVarName("f1");
      String o2 = quantVarName("o2");
      String f2 = quantVarName("f2");
      BPLVariable o1Var = new BPLVariable(o1, BPLBuiltInType.REF);
      BPLVariable f1Var = new BPLVariable(f1, BPLBuiltInType.NAME);
      BPLVariable o2Var = new BPLVariable(o2, BPLBuiltInType.REF);
      BPLVariable f2Var = new BPLVariable(f2, BPLBuiltInType.NAME);
      addAxiom(forall(
          o1Var, f1Var, o2Var, f2Var,
          isEquiv(
              isEqual(fieldLoc(var(o1), var(f1)), fieldLoc(var(o2), var(f2))),
              logicalAnd(
                  isEqual(var(o1), var(o2)),
                  isEqual(var(f1), var(f2))))));
    }

    {
      // An array element
      addFunction(
          ARRAY_LOC_FUNC,
          BPLBuiltInType.REF,
          BPLBuiltInType.INT,
          new BPLTypeName(LOCATION_TYPE));
      String o1 = quantVarName("o1");
      String i1 = quantVarName("i1");
      String o2 = quantVarName("o2");
      String i2 = quantVarName("i2");
      BPLVariable o1Var = new BPLVariable(o1, BPLBuiltInType.REF);
      BPLVariable i1Var = new BPLVariable(i1, BPLBuiltInType.INT);
      BPLVariable o2Var = new BPLVariable(o2, BPLBuiltInType.REF);
      BPLVariable i2Var = new BPLVariable(i2, BPLBuiltInType.INT);
      addAxiom(forall(
          o1Var, i1Var, o2Var, i2Var,
          isEquiv(
              isEqual(arrayLoc(var(o1), var(i1)), arrayLoc(var(o2), var(i2))),
              logicalAnd(
                  isEqual(var(o1), var(o2)),
                  isEqual(var(i1), var(i2))))));
    }

    {
      // instance fields and array elements
      String o1 = quantVarName("o1");
      String f1 = quantVarName("f1");
      String o2 = quantVarName("o2");
      String i2 = quantVarName("i2");
      BPLVariable o1Var = new BPLVariable(o1, BPLBuiltInType.REF);
      BPLVariable f1Var = new BPLVariable(f1, BPLBuiltInType.NAME);
      BPLVariable o2Var = new BPLVariable(o2, BPLBuiltInType.REF);
      BPLVariable i2Var = new BPLVariable(i2, BPLBuiltInType.INT);
      addAxiom(forall(
          o1Var, f1Var, o2Var, i2Var,
          notEqual(fieldLoc(var(o1), var(f1)), arrayLoc(var(o2), var(i2)))));
    }

    {
      // The object reference referring to an array element or instance variable
      addFunction(OBJ_FUNC, new BPLTypeName(LOCATION_TYPE), BPLBuiltInType.REF);
      String o = quantVarName("o");
      String f = quantVarName("f");
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      BPLVariable fVar = new BPLVariable(f, BPLBuiltInType.NAME);
      addAxiom(forall(
          oVar, fVar,
          isEqual(obj(fieldLoc(var(o), var(f))), var(o))));
      String i = quantVarName("i");
      oVar = new BPLVariable(o, BPLBuiltInType.REF);
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          oVar, iVar,
          isEqual(obj(arrayLoc(var(o), var(i))), var(o))));
    }

    {
      // Type of a location
      addFunction(
          LTYP_FUNC,
          new BPLTypeName(LOCATION_TYPE),
          BPLBuiltInType.NAME);
      String o = quantVarName("o");
      String f = quantVarName("f");
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      BPLVariable fVar = new BPLVariable(f, BPLBuiltInType.NAME);
      addAxiom(forall(
          oVar, fVar,
          isEqual(ltyp(fieldLoc(var(o), var(f))), fieldType(var(f)))));
      String i = quantVarName("i");
      oVar = new BPLVariable(o, BPLBuiltInType.REF);
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          oVar, iVar,
          isEqual(
              ltyp(arrayLoc(var(o), var(i))),
              elementType(typ(rval(var(o)))))));
    }

    // Field declaration
    addFunction(FIELD_TYPE_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.NAME);

    {
      // Static fields
      addFunction(TYPE_OBJECT_FUNC, BPLBuiltInType.NAME, BPLBuiltInType.REF);
      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(tVar, nonNull(typeObject(var(t)))));
      String h = quantVarName("h");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(hVar, tVar, alive(rval(typeObject(var(t))), var(h))));
    }

    //
    // An allocation is either an object of a specified class type or an array
    // of a specified element type
    //
    addTypes(ALLOCATION_TYPE);

    addFunction(
        OBJECT_ALLOC_FUNC,
        BPLBuiltInType.NAME,
        new BPLTypeName(ALLOCATION_TYPE));
    addFunction(
        ARRAY_ALLOC_FUNC,
        BPLBuiltInType.NAME,
        BPLBuiltInType.INT,
        new BPLTypeName(ALLOCATION_TYPE));
    addFunction(
        MULTI_ARRAY_ALLOC_FUNC,
        BPLBuiltInType.NAME,
        BPLBuiltInType.INT,
        new BPLTypeName(ALLOCATION_TYPE),
        new BPLTypeName(ALLOCATION_TYPE));

    {
      addFunction(
          ALLOC_TYPE_FUNC,
          new BPLTypeName(ALLOCATION_TYPE),
          BPLBuiltInType.NAME);
      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(tVar, isEqual(allocType(objectAlloc(var(t))), var(t))));

      String i = quantVarName("i");
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          tVar, iVar,
          isEqual(allocType(arrayAlloc(var(t), var(i))), arrayType(var(t)))));

      String a = quantVarName("a");
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          tVar, iVar, aVar,
          isEqual(
              allocType(multiArrayAlloc(var(t), var(i), var(a))),
              arrayType(var(t)))));
    }

    //
    // Heap functions
    //

    // Return the heap after storing a value in a location.
    addFunction(
        UPDATE_FUNC,
        new BPLTypeName(HEAP_TYPE),
        new BPLTypeName(LOCATION_TYPE),
        new BPLTypeName(VALUE_TYPE),
        new BPLTypeName(HEAP_TYPE));

    // Returns the heap after an object of the given type has been allocated.
    addFunction(
        ADD_FUNC,
        new BPLTypeName(HEAP_TYPE),
        new BPLTypeName(ALLOCATION_TYPE),
        new BPLTypeName(HEAP_TYPE));

    // Returns the value stored in a location.
    addFunction(
        GET_FUNC,
        new BPLTypeName(HEAP_TYPE),
        new BPLTypeName(LOCATION_TYPE),
        new BPLTypeName(VALUE_TYPE));

    // Returns true if a value is alive in a given heap.
    addFunction(
        ALIVE_FUNC,
        new BPLTypeName(VALUE_TYPE),
        new BPLTypeName(HEAP_TYPE),
        BPLBuiltInType.BOOL);

    // Returns a newly allocated object of the given type.
    addFunction(
        NEW_FUNC,
        new BPLTypeName(HEAP_TYPE),
        new BPLTypeName(ALLOCATION_TYPE),
        new BPLTypeName(VALUE_TYPE));

    //
    // Heap axioms
    //

    {
      // Field stores do not affect the values stored in other fields.
      String l1 = quantVarName("l1");
      String l2 = quantVarName("l2");
      String h = quantVarName("h");
      String v = quantVarName("v");
      BPLVariable l1Var = new BPLVariable(l1, new BPLTypeName(LOCATION_TYPE));
      BPLVariable l2Var = new BPLVariable(l2, new BPLTypeName(LOCATION_TYPE));
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          l1Var, l2Var, hVar, vVar,
          implies(
              notEqual(var(l1), var(l2)),
              isEqual(
                  get(update(var(h), var(l1), var(v)), var(l2)),
                  get(var(h), var(l2))))));
    }

    {
      // Field stores are persistent.
      String l = quantVarName("l");
      String h = quantVarName("h");
      String v = quantVarName("v");
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          lVar, hVar, vVar,
          implies(
              logicalAnd(
                  alive(rval(obj(var(l))), var(h)),
                  alive(var(v), var(h))),
              isEqual(get(update(var(h), var(l), var(v)), var(l)), var(v)))));
    }

    {
      // Object allocation does not affect the existing heap.
      String l = quantVarName("l");
      String h = quantVarName("h");
      String a = quantVarName("a");
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          lVar, hVar, aVar,
          isEqual(get(heapAdd(var(h), var(a)), var(l)), get(var(h), var(l)))));
    }

    {
      // Field stores do not affect object liveness.
      String l = quantVarName("l");
      String h = quantVarName("h");
      String v1 = quantVarName("v1");
      String v2 = quantVarName("v2");
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable v1Var = new BPLVariable(v1, new BPLTypeName(VALUE_TYPE));
      BPLVariable v2Var = new BPLVariable(v2, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          lVar, hVar, v1Var, v2Var,
          isEquiv(
              alive(var(v1), update(var(h), var(l), var(v2))),
              alive(var(v1), var(h)))));
    }

    {
      // An object is alive if it was already alive or if it is the new object.
      String h = quantVarName("h");
      String v = quantVarName("v");
      String a = quantVarName("a");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, vVar, aVar,
          implies(
              alive(var(v), var(h)),
              alive(var(v), heapAdd(var(h), var(a))))));

      hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, aVar,
          alive(heapNew(var(h), var(a)), heapAdd(var(h), var(a)))));
    }

    {
      // Values held stored in alive fields are themselves alive.
      String l = quantVarName("l");
      String h = quantVarName("h");
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      addAxiom(forall(
          lVar, hVar,
          implies(
              alive(rval(obj(var(l))), var(h)),
              alive(get(var(h), var(l)), var(h))),
          trigger(alive(get(var(h), var(l)), var(h)))));
    }

    {
      // Static values are always alive.
      String h = quantVarName("h");
      String v = quantVarName("v");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          hVar, vVar,
          implies(isStatic(var(v)), alive(var(v), var(h)))));
    }

    {
      // A newly allocated object is not alive in the heap it was created in.
      String h = quantVarName("h");
      String a = quantVarName("a");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, aVar,
          logicalNot(alive(heapNew(var(h), var(a)), var(h)))));
    }

    {
      // Allocated objects retain their type.
      String h = quantVarName("h");
      String a = quantVarName("a");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, aVar,
          isEqual(typ(heapNew(var(h), var(a))), allocType(var(a)))));
    }

    {
      // Creating an object of a given type in two heaps yields the same result
      // if liveness of all objects of that type is identical in both heaps.
      String h1 = quantVarName("h1");
      String h2 = quantVarName("h2");
      String a = quantVarName("a");
      String v = quantVarName("v");
      BPLVariable h1Var = new BPLVariable(h1, new BPLTypeName(HEAP_TYPE));
      BPLVariable h2Var = new BPLVariable(h2, new BPLTypeName(HEAP_TYPE));
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAxiom(forall(
          h1Var, h2Var, aVar,
          isEquiv(
              isEqual(heapNew(var(h1), var(a)), heapNew(var(h2), var(a))),
              forall(
                  vVar,
                  implies(
                      isEqual(typ(var(v)), allocType(var(a))),
                      isEquiv(
                          alive(var(v), var(h1)),
                          alive(var(v), var(h2))))))));
    }

    {
      // Two heaps are equal if they are indistinguishable by the alive and
      // get functions.
      String h1 = quantVarName("h1");
      String h2 = quantVarName("h2");
      String v = quantVarName("v");
      String l = quantVarName("l");
      BPLVariable h1Var = new BPLVariable(h1, new BPLTypeName(HEAP_TYPE));
      BPLVariable h2Var = new BPLVariable(h2, new BPLTypeName(HEAP_TYPE));
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      addAxiom(forall(
          h1Var, h2Var,
          implies(
              logicalAnd(
                  forall(
                      vVar,
                      isEquiv(alive(var(v), var(h1)), alive(var(v), var(h2)))),
                  forall(
                      lVar,
                      isEqual(get(var(h1), var(l)), get(var(h2), var(l))))),
              isEqual(var(h1), var(h2)))));
    }

    {
      // Get always returns either null or a value whose type is a subtype of
      // the (static) location type.
      String h = quantVarName("h");
      String l = quantVarName("l");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      addAxiom(forall(hVar, lVar, isOfType(get(var(h), var(l)), ltyp(var(l)))));
    }

    {
      // New arrays have the allocated length.
      String h = quantVarName("h");
      String t = quantVarName("t");
      String i = quantVarName("i");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          hVar, tVar, iVar,
          isEqual(
              arrayLength(heapNew(var(h), arrayAlloc(var(t), var(i)))),
              var(i))));

      String a = quantVarName("a");
      hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, tVar, iVar, aVar,
          isEqual(
              arrayLength(
                  heapNew(var(h), multiArrayAlloc(var(t), var(i), var(a)))),
              var(i))));
    }

    {
      // Multi-dimensional arrays
      addFunction(
          IS_MULTI_ARRAY_FUNC,
          new BPLTypeName(VALUE_TYPE),
          new BPLTypeName(HEAP_TYPE),
          new BPLTypeName(ALLOCATION_TYPE),
          BPLBuiltInType.BOOL);
      addFunction(
          MULTI_ARRAY_PARENT_FUNC,
          new BPLTypeName(VALUE_TYPE),
          new BPLTypeName(VALUE_TYPE));
      addFunction(
          MULTI_ARRAY_POSITION_FUNC,
          new BPLTypeName(VALUE_TYPE),
          BPLBuiltInType.INT);

      String h = quantVarName("h");
      String t = quantVarName("t");
      String i = quantVarName("i");
      String a = quantVarName("a");
      BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      BPLVariable aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      addAxiom(forall(
          hVar, tVar, iVar, aVar,
          isMultiArray(
              heapNew(var(h), multiArrayAlloc(var(t), var(i), var(a))),
              var(h),
              multiArrayAlloc(var(t), var(i), var(a)))));

      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          vVar, hVar, tVar, iVar,
          isEquiv(
              isMultiArray(var(v), var(h), arrayAlloc(var(t), var(i))),
              logicalAnd(
                  logicalNot(alive(var(v), var(h))),
                  isEqual(typ(var(v)), arrayType(var(t))),
                  isEqual(arrayLength(var(v)), var(i))))));

      String e = quantVarName("e");
      vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
      tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      iVar = new BPLVariable(i, BPLBuiltInType.INT);
      aVar = new BPLVariable(a, new BPLTypeName(ALLOCATION_TYPE));
      BPLVariable eVar = new BPLVariable(e, BPLBuiltInType.INT);
      addAxiom(forall(
          vVar, hVar, tVar, iVar, aVar,
          isEquiv(
              isMultiArray(var(v), var(h), multiArrayAlloc(var(t), var(i), var(a))),
              logicalAnd(
                  logicalNot(alive(var(v), var(h))),
                  isEqual(typ(var(v)), arrayType(var(t))),
                  isEqual(arrayLength(var(v)), var(i)),
                  forall(
                      eVar,
                      logicalAnd(
                          isMultiArray(get(var(h), arrayLoc(toref(var(v)), var(e))), var(h), var(a)),
                          isEqual(
                              multiArrayParent(get(var(h), arrayLoc(toref(var(v)), var(e)))),
                              var(v)),
                          isEqual(
                              multiArrayPosition(get(var(h), arrayLoc(toref(var(v)), var(e)))),
                              var(e))))))));
    }
  }

  /**
   * Axiomatizes some aspects of the JVM type system.
   */
  private void axiomatizeTypeSystem() {
    {
      JType object = TypeLoader.getClassType("java.lang.Object");
      JType cloneable = TypeLoader.getClassType("java.lang.Cloneable");
      JType serializable = TypeLoader.getClassType("java.io.Serializable");

      String t = quantVarName("t");
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          tVar,
          logicalAnd(
              isSubtype(arrayType(var(t)), typeRef(object)),
              isSubtype(arrayType(var(t)), typeRef(cloneable)),
              isSubtype(arrayType(var(t)), typeRef(serializable)))));

      String t1 = quantVarName("t1");
      String t2 = quantVarName("t2");
      BPLVariable t1Var = new BPLVariable(t1, BPLBuiltInType.NAME);
      BPLVariable t2Var = new BPLVariable(t2, BPLBuiltInType.NAME);
      addAxiom(forall(
          t1Var, t2Var,
          implies(
              isSubtype(var(t1), var(t2)),
              isSubtype(arrayType(var(t1)), arrayType(var(t2))))));

      t1Var = new BPLVariable(t1, BPLBuiltInType.NAME);
      t2Var = new BPLVariable(t2, BPLBuiltInType.NAME);
      addAxiom(forall(
          t1Var, t2Var,
          implies(
              isSubtype(var(t1), arrayType(var(t2))),
              logicalAnd(
                  isEqual(var(t1), arrayType(elementType(var(t1)))),
                  isSubtype(elementType(var(t1)), var(t2)))),
          trigger(isSubtype(var(t1), arrayType(var(t2))))));
    }
  }

  /**
   * Defines and axiomatizes some simple helper functions.
   */
  private void axiomatizeHelperFunctions() {
    {
      // A helper function for converting bool values to int values.
      addFunction(BOOL2INT_FUNC, BPLBuiltInType.BOOL, BPLBuiltInType.INT);

      String b = quantVarName("b");
      BPLVariable bVar = new BPLVariable(b, BPLBuiltInType.BOOL);
      addAxiom(forall(
          bVar,
          isEquiv(
              isEqual(bool2int(var(b)), intLiteral(0)),
              isEqual(var(b), BPLBoolLiteral.FALSE))));

      bVar = new BPLVariable(b, BPLBuiltInType.BOOL);
      addAxiom(forall(
          bVar,
          isEquiv(
              notEqual(bool2int(var(b)), intLiteral(0)),
              isEqual(var(b), BPLBoolLiteral.TRUE))));
    }

    {
      // A helper function for converting int values to bool values.
      addFunction(INT2BOOL_FUNC, BPLBuiltInType.INT, BPLBuiltInType.BOOL);

      String i = quantVarName("i");
      BPLVariable iVar = new BPLVariable(i, BPLBuiltInType.INT);
      addAxiom(forall(
          iVar,
          isEquiv(
              isEqual(int2bool(var(i)), BPLBoolLiteral.FALSE),
              isEqual(var(i), intLiteral(0)))));

      addAxiom(forall(
          iVar,
          isEquiv(
              isEqual(int2bool(var(i)), BPLBoolLiteral.TRUE),
              notEqual(var(i), intLiteral(0)))));
    }

    {
      addFunction(
          IS_OF_TYPE_FUNC,
          new BPLTypeName(VALUE_TYPE),
          BPLBuiltInType.NAME,
          BPLBuiltInType.BOOL);
      String v = quantVarName("v");
      String t = quantVarName("t");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      // A value is of a given type if and only if it is the null value or if
      // its type is a subtype of the given type.
      addAxiom(forall(
          vVar, tVar,
          isEquiv(
              isOfType(var(v), var(t)),
              logicalOr(
                  isEqual(var(v), rval(nullLiteral())),
                  isSubtype(typ(var(v)), var(t))))));
    }

    {
      addFunction(
          IS_INSTANCE_OF_FUNC,
          new BPLTypeName(VALUE_TYPE),
          BPLBuiltInType.NAME,
          BPLBuiltInType.BOOL);
      String v = quantVarName("v");
      String t = quantVarName("t");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      // A value is an instance of a given type if and only if it is not the
      // null value and if its type is a subtype of the given type.
      addAxiom(forall(
          vVar, tVar,
          isEquiv(
              isInstanceOf(var(v), var(t)),
              logicalAnd(
                  notEqual(var(v), rval(nullLiteral())),
                  isSubtype(typ(var(v)), var(t))))));
    }

    // The function used for the declaration of object invariants.
    addFunction(
        INV_FUNC,
        BPLBuiltInType.NAME,
        BPLBuiltInType.REF,
        new BPLTypeName(HEAP_TYPE),
        BPLBuiltInType.BOOL);
  }

  /**
   * Method in which all the pending background theory for which information
   * has been collected during the actual translation of the bytecode methods
   * can be added to the BoogiePL program. This method is thought for those
   * parts of the background theory which can only be generated once all the
   * bytecode methods have been translated. Therefore, it should be invoked
   * right before assembling the BoogiePL program after the translation of
   * all bytecode methods.
   */
  private void flushPendingTheory() {
    // If we have generated symbolic constants representing large integer
    // values, we axiomatize their relative order in order maintain as much
    // information as possible.
    if (context.symbolicIntLiterals.size() > 0) {
      // The requested iterator gives us the integers in ascending order.
      Iterator<Integer> intConstants = context.symbolicIntLiterals.iterator();
      int current = intConstants.next();
      int maxConstant = project.getMaxIntConstant();
      // Handle the negative values.
      while ((current < 0) && intConstants.hasNext()) {
        int next = intConstants.next();
        if (next < 0) {
          // If the next integer is still negative, we simply state that the
          // current integer is less than the next one.
          addAxiom(less(intLiteral(current), intLiteral(next)));
        } else {
          // If the next integer is positive, we state that the current integer
          // is less than the lowest integer value explicitly represented in the
          // BoogiePL program but we do not relate the current negative
          // integer to the next one which is positive.
          addAxiom(less(intLiteral(current), intLiteral(-maxConstant)));
        }
        current = next;
      }
      if (current < 0) {
        // If the current integer is still negative, the above loop guard tells
        // us that there are no more integers to process but we must still
        // relate the current negative integer to the lowest integer value
        // explicitly represented in the BoogiePL program.
        addAxiom(less(intLiteral(current), intLiteral(-maxConstant)));
      } else {
        // If the current integer is positive, we relate it to the largest
        // integer value explicitly represented in the BoogiePL program.
        addAxiom(less(intLiteral(maxConstant), intLiteral(current)));
      }
      while (intConstants.hasNext()) {
        // Likewise, axiomatize the relative order of the remaining integers
        // which must be all positive.
        int next = intConstants.next();
        addAxiom(less(intLiteral(current), intLiteral(next)));
        current = next;
      }
    }
  }

  /**
   * Adds an axiom representing the <code>type</code>'s object invariant.
   *
   * @param type  The class type whose object invariant should be translated.
   */
  private void addInvariantDeclaration(JClassType type) {
    // Get the actual invariant predicate as declared in the given class
    // (not including the invariants declared in superclasses).
    BMLExpression invariant =
      project.getSpecificationDesugarer().getObjectInvariant(type, true);

    String o = quantVarName("o");
    String h = quantVarName("h");

    SpecificationTranslator translator =
      SpecificationTranslator.forInvariant(h, o);

    BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
    BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
    // An invariant hold for a given object if and only if the object is an
    // instance of the class in which the invariant is declared and if the
    // actual invariant predicate holds in for the given object in the given
    // heap.
    addAxiom(forall(
        oVar, hVar,
        isEquiv(
            inv(typeRef(type), var(o), var(h)),
            implies(
                isInstanceOf(rval(var(o)), typeRef(type)),
                translator.translate(context, invariant)))));
  }

  /**
   * Implementation of the {@link TranslationContext} interface which handles
   * the translation of different kinds of references.
   *
   * @author Ovidio Mallo
   */
  private final class Context implements TranslationContext {

    /** The types referenced during the translation. */
    private HashSet<JClassType> typeReferences;

    /** The fields referenced during the translation. */
    private HashSet<BCField> fieldReferences;

    /**
     * The integers encountered during the translation which are not represented
     * as such in the generated BoogiePL program but by symbolic constants
     * instead.
     */
    private TreeSet<Integer> symbolicIntLiterals;

    /** The string literals encountered during the translation. */
    private HashMap<String, String> stringLiterals;

    /** The class literals encountered during the translation. */
    private HashSet<JType> classLiterals;

    /**
     * Initializes the internal datastructures.
     */
    public Context() {
      typeReferences = new HashSet<JClassType>();
      fieldReferences = new HashSet<BCField>();
      symbolicIntLiterals = new TreeSet<Integer>();
      stringLiterals = new HashMap<String, String>();
      classLiterals = new HashSet<JType>();
    }

    /**
     * Generates an axiom for the given <code>type</code> which rules out
     * "wrong supertypes" of that <code>type</code> by contradiction. This
     * makes it possible for the program verifier to not only show whether some
     * type indeed is a supertype of the given <code>type</code> but also
     * whether it is <i>not</i> a supertype.
     *
     * @param type  The class type to axiomatize.
     */
    private void translateSubtyping(JClassType type) {
      // Recursively state that if some type t is a supertype of the given type,
      // then t must be the type itself, or else, it is a supertype of one of
      // the type's direct supertypes.
      String t = quantVarName("t");
      BPLExpression axiom = isEqual(var(t), translateTypeReference(type));
      JClassType supertype = type.getSupertype();
      if (supertype != null) {
        addAxiom(isSubtype(typeRef(type), typeRef(supertype)));
        axiom = logicalOr(
            axiom,
            isSubtype(translateTypeReference(supertype), var(t)));
      }
      for (JClassType iface : type.getInterfaces()) {
        addAxiom(isSubtype(typeRef(type), typeRef(supertype)));
        axiom = logicalOr(
            axiom,
            isSubtype(translateTypeReference(iface), var(t)));
      }
      BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
      addAxiom(forall(
          tVar,
          implies(isSubtype(translateTypeReference(type), var(t)), axiom),
          trigger(isSubtype(translateTypeReference(type), var(t)))));
    }

    /**
     * Translates the given <code>type</code> reference. The translation of a
     * new type reference thereby triggers the generation of the following
     * declarations in the BoogiePL program:
     * <ul>
     *   <li>
     *     A <i>name</i> constant representing the given <code>type</code> is
     *     declared.
     *   </li>
     *   <li>
     *     If the given <code>type</code> is final, an appropriate axiom
     *     expressing this fact is generated.
     *   </li>
     *   <li>
     *     A set of axioms defining the supertype hierarchy of the given
     *     <code>type</code> is generated.
     *   </li>
     *   <li>
     *     An axiom expressing the <code>type</code>'s object invariant is
     *     generated.
     *   </li>
     * </ul>
     * The returned <code>BPLExpression</code> is guaranteed to be of type
     * <i>name</i>.
     */
    public BPLExpression translateTypeReference(JType type) {
      // Only class types trigger the translation of constants representing
      // them.
      if (type.isClassType() && !typeReferences.contains(type)) {
        JClassType classType = (JClassType) type;
        typeReferences.add(classType);

        // Declare the constant representing the given class type.
        addConstants(new BPLVariable(
            getClassTypeName(classType),
            BPLBuiltInType.NAME));

        // State that the type indeed is a class type.
        addAxiom(isClassType(typeRef(classType)));

        // Eventually axiomatize the fact that the type is final.
        if (classType.isFinal()) {
          String t = quantVarName("t");
          BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
          // Every eventual subtype must be the type itself.
          addAxiom(forall(
              tVar,
              implies(
                  isSubtype(var(t), typeRef(classType)),
                  isEqual(var(t), typeRef(classType))),
              trigger(isSubtype(var(t), typeRef(classType)))));
        }

        // Generate axioms for ruling out "wrong supertypes".
        translateSubtyping(classType);

        // For every referenced class type, we generate an axiom representing
        // its object invariant.
        addInvariantDeclaration(classType);
      }

      // Now, do the actual translation of the type reference to be used in the
      // BoogiePL program.
      if (type.isBaseType()) {
        return var(getValueTypeName((JBaseType) type));
      } else if (type.isClassType()) {
        return var(getClassTypeName((JClassType) type));
      } else {
        // We must have an array type.
        JArrayType arrayType = (JArrayType) type;
        BPLExpression typeExpr =
          translateTypeReference(arrayType.getComponentType());
        for (int i = 0; i < arrayType.getDimension(); i++) {
          typeExpr = arrayType(typeExpr);
        }
        return typeExpr;
      }
    }

    /**
     * Translates the given <code>field</code> reference. The translation of a
     * new field reference thereby triggers the generation of the following
     * declarations in the BoogiePL program:
     * <ul>
     *   <li>
     *     A <i>name</i> constant representing the given <code>type</code> is
     *     declared.
     *   </li>
     *   <li>
     *     An axiom defining the <code>field</code>'s declared type is
     *     generated.
     *   </li>
     *   <li>
     *     The <code>field</code>'s owner type is translated.
     *   </li>
     * </ul>
     * The returned <code>BPLExpression</code> is guaranteed to be of type
     * <i>name</i>.
     */
    public BPLExpression translateFieldReference(BCField field) {
      String fieldName = field.getQualifiedName();
      if (!fieldReferences.contains(field)) {
        fieldReferences.add(field);

        // Declare the constant representing the given field.
        addConstants(new BPLVariable(fieldName, BPLBuiltInType.NAME));

        // Define the field's declared type.
        addAxiom(isEqual(
            fieldType(var(fieldName)),
            translateTypeReference(field.getType())));

        // For every field referenced, we also translate its owner type.
        translateTypeReference(field.getOwner());
      }
      return var(fieldName);
    }

    /**
     * Translates the given integer <code>literal</code>. If the integer's
     * magnitude is less or equal to the value returned by the
     * {@link Project#getMaxIntConstant()} method of the current project,
     * the integer is translated as is to BoogiePL. Otherwise, it is replaced
     * by a special constant representing its value.
     * The returned <code>BPLExpression</code> is guaranteed to be of type
     * <i>int</i>.
     */
    public BPLExpression translateIntLiteral(int literal) {
      // If the integer value is in the desired range, the literal is translated
      // as is.
      if ((-project.getMaxIntConstant() <= literal)
          && (literal <= project.getMaxIntConstant())) {
        return new BPLIntLiteral(literal);
      }

      // If the integer's magnitude is too large, we represent it by a symbolic
      // constant.
      if (symbolicIntLiterals.add(literal)) {
        addConstants(new BPLVariable(
            getSymbolicIntLiteralName(literal),
            BPLBuiltInType.INT));
      }
      return var(getSymbolicIntLiteralName(literal));
    }

    /**
     * Translates the given string <code>literal</code>.
     * The returned <code>BPLExpression</code> is guaranteed to be of type
     * <i>ref</i>.
     */
    public BPLExpression translateStringLiteral(String literal) {
      if (stringLiterals.get(literal) == null) {
        String name = STRING_LITERAL_PREFIX + stringLiterals.size();
        stringLiterals.put(literal, name);

        // Declare the constant representing the given field.
        addConstants(new BPLVariable(name, BPLBuiltInType.REF));

        // State that the object representing the literal is of type String and
        // that it is alive in any heap.
        JType string = TypeLoader.getClassType("java.lang.String");
        String h = quantVarName("h");
        BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
        addAxiom(forall(
            hVar,
            logicalAnd(
                isInstanceOf(rval(var(name)), typeRef(string)),
                alive(rval(var(name)), var(h)))));
      }
      return var(stringLiterals.get(literal));
    }

    /**
     * Translates the given class <code>literal</code>.
     * The returned <code>BPLExpression</code> is guaranteed to be of type
     * <i>ref</i>.
     */
    public BPLExpression translateClassLiteral(JType literal) {
      String name =
        GLOBAL_VAR_PREFIX + literal.getName() + CLASS_LITERAL_SUFFIX;
      if (classLiterals.add(literal)) {
        // Declare the constant representing the given field.
        addConstants(new BPLVariable(name, BPLBuiltInType.REF));

        // State that the object representing the literal is of type Class and
        // that it is alive in any heap.
        JType clazz = TypeLoader.getClassType("java.lang.Class");
        String h = quantVarName("h");
        BPLVariable hVar = new BPLVariable(h, new BPLTypeName(HEAP_TYPE));
        addAxiom(forall(
            hVar,
            logicalAnd(
                isInstanceOf(rval(var(name)), typeRef(clazz)),
                alive(rval(var(name)), var(h)))));
      }
      return var(name);
    }
  }
}
