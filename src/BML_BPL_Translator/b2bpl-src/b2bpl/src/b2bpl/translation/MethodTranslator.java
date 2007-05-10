package b2bpl.translation;

import static b2bpl.translation.CodeGenerator.add;
import static b2bpl.translation.CodeGenerator.alive;
import static b2bpl.translation.CodeGenerator.arrayAccess;
import static b2bpl.translation.CodeGenerator.arrayAlloc;
import static b2bpl.translation.CodeGenerator.arrayLength;
import static b2bpl.translation.CodeGenerator.arrayUpdate;
import static b2bpl.translation.CodeGenerator.bitAnd;
import static b2bpl.translation.CodeGenerator.bitOr;
import static b2bpl.translation.CodeGenerator.bitShl;
import static b2bpl.translation.CodeGenerator.bitShr;
import static b2bpl.translation.CodeGenerator.bitUShr;
import static b2bpl.translation.CodeGenerator.bitXor;
import static b2bpl.translation.CodeGenerator.bool2int;
import static b2bpl.translation.CodeGenerator.cast;
import static b2bpl.translation.CodeGenerator.divide;
import static b2bpl.translation.CodeGenerator.elementType;
import static b2bpl.translation.CodeGenerator.fieldAccess;
import static b2bpl.translation.CodeGenerator.fieldLoc;
import static b2bpl.translation.CodeGenerator.fieldUpdate;
import static b2bpl.translation.CodeGenerator.forall;
import static b2bpl.translation.CodeGenerator.get;
import static b2bpl.translation.CodeGenerator.greater;
import static b2bpl.translation.CodeGenerator.greaterEqual;
import static b2bpl.translation.CodeGenerator.heapAdd;
import static b2bpl.translation.CodeGenerator.heapAddArray;
import static b2bpl.translation.CodeGenerator.heapNew;
import static b2bpl.translation.CodeGenerator.heapNewArray;
import static b2bpl.translation.CodeGenerator.icast;
import static b2bpl.translation.CodeGenerator.ifThenElse;
import static b2bpl.translation.CodeGenerator.implies;
import static b2bpl.translation.CodeGenerator.inv;
import static b2bpl.translation.CodeGenerator.isEqual;
import static b2bpl.translation.CodeGenerator.isExceptionalReturnState;
import static b2bpl.translation.CodeGenerator.isInstanceOf;
import static b2bpl.translation.CodeGenerator.isNormalReturnState;
import static b2bpl.translation.CodeGenerator.isNull;
import static b2bpl.translation.CodeGenerator.isOfType;
import static b2bpl.translation.CodeGenerator.ival;
import static b2bpl.translation.CodeGenerator.less;
import static b2bpl.translation.CodeGenerator.lessEqual;
import static b2bpl.translation.CodeGenerator.logicalAnd;
import static b2bpl.translation.CodeGenerator.logicalNot;
import static b2bpl.translation.CodeGenerator.logicalOr;
import static b2bpl.translation.CodeGenerator.modulo;
import static b2bpl.translation.CodeGenerator.multiArrayAlloc;
import static b2bpl.translation.CodeGenerator.multiply;
import static b2bpl.translation.CodeGenerator.neg;
import static b2bpl.translation.CodeGenerator.nonNull;
import static b2bpl.translation.CodeGenerator.notEqual;
import static b2bpl.translation.CodeGenerator.nullLiteral;
import static b2bpl.translation.CodeGenerator.obj;
import static b2bpl.translation.CodeGenerator.old;
import static b2bpl.translation.CodeGenerator.quantVarName;
import static b2bpl.translation.CodeGenerator.rval;
import static b2bpl.translation.CodeGenerator.sub;
import static b2bpl.translation.CodeGenerator.typ;
import static b2bpl.translation.CodeGenerator.type;
import static b2bpl.translation.CodeGenerator.var;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import b2bpl.Main;
import b2bpl.Project;
import b2bpl.bpl.ast.BPLAssertCommand;
import b2bpl.bpl.ast.BPLAssignmentCommand;
import b2bpl.bpl.ast.BPLAssumeCommand;
import b2bpl.bpl.ast.BPLBasicBlock;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLCallCommand;
import b2bpl.bpl.ast.BPLCommand;
import b2bpl.bpl.ast.BPLEnsuresClause;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLGotoCommand;
import b2bpl.bpl.ast.BPLHavocCommand;
import b2bpl.bpl.ast.BPLImplementation;
import b2bpl.bpl.ast.BPLImplementationBody;
import b2bpl.bpl.ast.BPLModifiesClause;
import b2bpl.bpl.ast.BPLNullLiteral;
import b2bpl.bpl.ast.BPLProcedure;
import b2bpl.bpl.ast.BPLRequiresClause;
import b2bpl.bpl.ast.BPLReturnCommand;
import b2bpl.bpl.ast.BPLSpecification;
import b2bpl.bpl.ast.BPLSpecificationClause;
import b2bpl.bpl.ast.BPLTransferCommand;
import b2bpl.bpl.ast.BPLType;
import b2bpl.bpl.ast.BPLTypeName;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bpl.ast.BPLVariableDeclaration;
import b2bpl.bpl.ast.BPLVariableExpression;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.BCMethod;
import b2bpl.bytecode.ExceptionHandler;
import b2bpl.bytecode.IInstructionVisitor;
import b2bpl.bytecode.IOpCodes;
import b2bpl.bytecode.InstructionHandle;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JClassType;
import b2bpl.bytecode.JNullType;
import b2bpl.bytecode.JType;
import b2bpl.bytecode.TypeLoader;
import b2bpl.bytecode.analysis.BasicBlock;
import b2bpl.bytecode.analysis.ControlFlowGraph;
import b2bpl.bytecode.analysis.Edge;
import b2bpl.bytecode.analysis.StackFrame;
import b2bpl.bytecode.bml.ast.BMLExpression;
import b2bpl.bytecode.bml.ast.BMLIntLiteral;
import b2bpl.bytecode.bml.ast.BMLLoopInvariant;
import b2bpl.bytecode.bml.ast.BMLLoopModifiesClause;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.bml.ast.BMLLoopVariant;
import b2bpl.bytecode.bml.ast.BMLMethodSpecification;
import b2bpl.bytecode.bml.ast.BMLSpecificationCase;
import b2bpl.bytecode.bml.ast.BMLStoreRef;
import b2bpl.bytecode.instructions.AALoadInstruction;
import b2bpl.bytecode.instructions.AAStoreInstruction;
import b2bpl.bytecode.instructions.AConstNullInstruction;
import b2bpl.bytecode.instructions.ALoadInstruction;
import b2bpl.bytecode.instructions.ANewArrayInstruction;
import b2bpl.bytecode.instructions.AReturnInstruction;
import b2bpl.bytecode.instructions.AStoreInstruction;
import b2bpl.bytecode.instructions.AThrowInstruction;
import b2bpl.bytecode.instructions.AbstractIfInstruction;
import b2bpl.bytecode.instructions.ArrayLengthInstruction;
import b2bpl.bytecode.instructions.CheckCastInstruction;
import b2bpl.bytecode.instructions.Dup2Instruction;
import b2bpl.bytecode.instructions.Dup2X1Instruction;
import b2bpl.bytecode.instructions.Dup2X2Instruction;
import b2bpl.bytecode.instructions.DupInstruction;
import b2bpl.bytecode.instructions.DupX1Instruction;
import b2bpl.bytecode.instructions.DupX2Instruction;
import b2bpl.bytecode.instructions.GetFieldInstruction;
import b2bpl.bytecode.instructions.GetStaticInstruction;
import b2bpl.bytecode.instructions.GotoInstruction;
import b2bpl.bytecode.instructions.IBinArithInstruction;
import b2bpl.bytecode.instructions.IBitwiseInstruction;
import b2bpl.bytecode.instructions.IIncInstruction;
import b2bpl.bytecode.instructions.ILoadInstruction;
import b2bpl.bytecode.instructions.INegInstruction;
import b2bpl.bytecode.instructions.IReturnInstruction;
import b2bpl.bytecode.instructions.IStoreInstruction;
import b2bpl.bytecode.instructions.IfACmpInstruction;
import b2bpl.bytecode.instructions.IfICmpInstruction;
import b2bpl.bytecode.instructions.IfInstruction;
import b2bpl.bytecode.instructions.IfNonNullInstruction;
import b2bpl.bytecode.instructions.IfNullInstruction;
import b2bpl.bytecode.instructions.InstanceOfInstruction;
import b2bpl.bytecode.instructions.InvokeInstruction;
import b2bpl.bytecode.instructions.InvokeInterfaceInstruction;
import b2bpl.bytecode.instructions.InvokeSpecialInstruction;
import b2bpl.bytecode.instructions.InvokeStaticInstruction;
import b2bpl.bytecode.instructions.InvokeVirtualInstruction;
import b2bpl.bytecode.instructions.LBinArithInstruction;
import b2bpl.bytecode.instructions.LBitwiseInstruction;
import b2bpl.bytecode.instructions.LCmpInstruction;
import b2bpl.bytecode.instructions.LLoadInstruction;
import b2bpl.bytecode.instructions.LNegInstruction;
import b2bpl.bytecode.instructions.LReturnInstruction;
import b2bpl.bytecode.instructions.LStoreInstruction;
import b2bpl.bytecode.instructions.LdcInstruction;
import b2bpl.bytecode.instructions.LookupSwitchInstruction;
import b2bpl.bytecode.instructions.MultiANewArrayInstruction;
import b2bpl.bytecode.instructions.NewArrayInstruction;
import b2bpl.bytecode.instructions.NewInstruction;
import b2bpl.bytecode.instructions.NopInstruction;
import b2bpl.bytecode.instructions.Pop2Instruction;
import b2bpl.bytecode.instructions.PopInstruction;
import b2bpl.bytecode.instructions.PutFieldInstruction;
import b2bpl.bytecode.instructions.PutStaticInstruction;
import b2bpl.bytecode.instructions.ReturnInstruction;
import b2bpl.bytecode.instructions.SwapInstruction;
import b2bpl.bytecode.instructions.TableSwitchInstruction;
import b2bpl.bytecode.instructions.VALoadInstruction;
import b2bpl.bytecode.instructions.VAStoreInstruction;
import b2bpl.bytecode.instructions.VCastInstruction;
import b2bpl.bytecode.instructions.VConstantInstruction;


/**
 * The main entry point to the translation of a bytecode method to a BoogiePL
 * procedure.
 * 
 * <p>
 * Some aspects of the translation process can be configured by passing an
 * appropriate {@link Project} instance containing the desired translation
 * settings upon creating the {@code MethodTranslator}. In particular, the
 * following aspects of the translation can be configured:
 * <ul>
 * <li> The verification methodology for object invariants (see
 * {@link Project#isThisInvariantsOnly()}). </li>
 * <li> Whether to explicitly model runtime exceptions instead of ruling them
 * out by verification conditions (see
 * {@link Project#isModelRuntimeExceptions()}). </li>
 * </ul>
 * </p>
 * 
 * <p>
 * The {@code MethodTranslator} is responsible for the following aspects of the
 * translation process:
 * <ul>
 * <li> The translation of the individual bytecode instructions and the method's
 * program flow. </li>
 * <li> The generation of a set of assumptions justified by the JVM environment.
 * This mainly includes the translation of the method's static type information
 * but also the modeling of properties guaranteed by the JVM such as the fact
 * that the this object is never aliased at the beginning of a constructor.
 * </li>
 * <li> The translation of the local BML specifications such as assertions,
 * assumptions, and loop specifications. </li>
 * <li> The generation of proof obligations as well as assumptions as required
 * or justified, respectively, by the verification methodology used. This mainly
 * includes the handling of object invariants and method specifications
 * according to the verification methodology. </li>
 * </ul>
 * The actual translation of BML specification expressions and store references
 * is thereby not performed directly by the {@code MethodTranslator} but instead
 * delegated to the {@link SpecificationTranslator} and {@link ModifiesFilter}
 * classes, respectively.
 * </p>
 * 
 * @see Project#isThisInvariantsOnly()
 * @see Project#isModelRuntimeExceptions()
 * @see SpecificationTranslator
 * @see ModifiesFilter
 * 
 * @author Ovidio Mallo, Samuel Willimann
 */
public class MethodTranslator implements ITranslationConstants {

  /** The project containing the settings of the translation. */
  private final Project project;

  /**
   * The translation context to be used during the translation of the current
   * bytecode method.
   */
  private ITranslationContext context;

  /** The bytecode method currently being translated. */
  private BCMethod method;

  /**
   * The label of the current BoogiePL basic block or {@code null} if no such
   * block is active at the moment.
   */
  private String blockLabel;

  /**
   * A list for accumulating BoogiePL commands inside a basic block during the
   * translation.
   */
  private List<BPLCommand> commands;

  /**
   * A list for accumulating BoogiePL basic blocks inside the procedure during
   * the translation.
   */
  private List<BPLBasicBlock> blocks;

  /**
   * The variables which store a copy of the current heap at each loop header.
   * These variables are dynamically "allocated" during the translation of the
   * method.
   */
  private HashMap<BasicBlock, String> loopHeapVars;

  /**
   * The variables which store the value of loop variant expressions at each
   * loop header. These variables are dynamically "allocated" during the
   * translation of the method.
   */
  private HashMap<BMLLoopVariant, String> loopVariantVars;

  /**
   * Number of call statements in the current method. For every individual call
   * statement, a fresh set of variables (return state and return value) is
   * used.
   */
  private int callStatements = 0;

  /**
   * Creates a new method translator which is configured by the given
   * {@code project}. Once a translator has been created, it can be used to
   * translate different bytecode methods under the same configuration (given by
   * the here provided {@code project}).
   * 
   * @param project The project containing the configurations of the
   *          translation.
   * 
   * @see #translate(ITranslationContext, BCMethod)
   */
  public MethodTranslator(Project project) {
    this.project = project;
  }

  /**
   * Performs the actual translation of the given bytecode {@code method} and
   * returns a BoogiePL procedure representing it.
   * 
   * @param context The {@code TranslationContext} to be used for translating
   *          type/field/constant/... references.
   * @param method The bytecode method to be translated.
   * @return The BoogiePL procedure resulting from the translation of the given
   *         bytecode method.
   */
  public BPLProcedure translate(ITranslationContext context, BCMethod method) {
    this.context = context;
    this.method = method;
    initTranslation();
    translateInit();
    // translatePre();
    translateInstructions();
    translatePost();
    return buildProcedure();
  }

  /**
   * Builds and the return the actual BoogiePL procedure resulting from the
   * translation of the bytecode method. This method should be called once the
   * actual translation of the method body has finished.
   * 
   * @return The BoogiePL procedure resulting from the translation of the given
   *         bytecode method.
   */
  private BPLProcedure buildProcedure() {
    List<BPLVariableDeclaration> vars = new ArrayList<BPLVariableDeclaration>();

    // The local variables.
    for (int i = 0; i < method.getMaxLocals(); i++) {
      BPLVariable regr = new BPLVariable(refLocalVar(i), BPLBuiltInType.REF);
      BPLVariable regi = new BPLVariable(intLocalVar(i), BPLBuiltInType.INT);
      // vars.add(new BPLVariableDeclaration(regr, regi));
      vars.add(filterVariableDeclarations(blocks, regr, regi));
    }

    // The stack variables.
    for (int i = 0; i < method.getMaxStack(); i++) {
      BPLVariable stackr = new BPLVariable(refStackVar(i), BPLBuiltInType.REF);
      BPLVariable stacki = new BPLVariable(intStackVar(i), BPLBuiltInType.INT);
      // vars.add(new BPLVariableDeclaration(stackr, stacki));
      vars.add(filterVariableDeclarations(blocks, stackr, stacki));
    }

    // Return variables for method calls
    for (int i = 0; i < callStatements; i++) {
      BPLVariable rs = new BPLVariable(returnStateVar(i), new BPLTypeName(
          RETURN_STATE_TYPE));
      BPLVariable rvr = new BPLVariable(
          refReturnValueVar(i),
          BPLBuiltInType.REF);
      BPLVariable rvi = new BPLVariable(
          intReturnValueVar(i),
          BPLBuiltInType.INT);
      BPLVariable exr = new BPLVariable(exceptionVar(i), BPLBuiltInType.REF);
      vars.add(filterVariableDeclarations(blocks, rs, rvr, rvi, exr));
    }

    // Helper variables for storing the return value of a method call.
    BPLVariable callResultr = new BPLVariable(
        REF_CALL_RESULT_VAR,
        BPLBuiltInType.REF);
    BPLVariable callResulti = new BPLVariable(
        INT_CALL_RESULT_VAR,
        BPLBuiltInType.INT);
    // vars.add(new BPLVariableDeclaration(callResultr, callResulti));
    vars.add(filterVariableDeclarations(blocks, callResultr, callResulti));

    // Helper variables for swapping two values.
    BPLVariable swapr = new BPLVariable(REF_SWAP_VAR, BPLBuiltInType.REF);
    BPLVariable swapi = new BPLVariable(INT_SWAP_VAR, BPLBuiltInType.INT);
    // vars.add(new BPLVariableDeclaration(swapr, swapi));
    vars.add(filterVariableDeclarations(blocks, swapr, swapi));

    // The diverse heap variables being maintained.
    /*
    BPLVariable heap = new BPLVariable(HEAP_VAR, new BPLTypeName(HEAP_TYPE));
    BPLVariable oldHeap = new BPLVariable(OLD_HEAP_VAR, new BPLTypeName(HEAP_TYPE));
    BPLVariable preHeap = new BPLVariable(PRE_HEAP_VAR, new BPLTypeName(HEAP_TYPE));
    vars.add(new BPLVariableDeclaration(heap, oldHeap, preHeap));
    vars.add(filterVariableDeclarations(blocks, heap, oldHeap, preHeap));
    */

    // The variables which store a copy of the current heap at each loop header.
    // These variables are dynamically "allocated" during the translation of the
    // method.
    if (loopHeapVars.size() > 0) {
      List<BPLVariable> lhVars = new ArrayList<BPLVariable>();
      for (String loopHeapVar : loopHeapVars.values()) {
        lhVars.add(new BPLVariable(loopHeapVar, new BPLTypeName(HEAP_TYPE)));
      }
      vars.add(new BPLVariableDeclaration(lhVars.toArray(new BPLVariable[lhVars.size()])));
    }

    // The variables which store the value of loop variant expressions at each
    // loop header. These variables are dynamically "allocated" during the
    // translation of the method.
    if (loopVariantVars.size() > 0) {
      List<BPLVariable> lvVars = new ArrayList<BPLVariable>();
      for (String loopHeapVar : loopVariantVars.values()) {
        lvVars.add(new BPLVariable(loopHeapVar, BPLBuiltInType.INT));
      }
      vars.add(new BPLVariableDeclaration(lvVars.toArray(new BPLVariable[lvVars.size()])));
    }

    // Build the different parts of the BoogiePL procedure.
    String name = getProcedureName(method);
    BPLImplementationBody body = new BPLImplementationBody(
        vars.toArray(new BPLVariableDeclaration[vars.size()]),
        blocks.toArray(new BPLBasicBlock[blocks.size()]));

    boolean provideReturnValue = !method.isVoid() || method.isConstructor();
    
    JType[] paramTypes = method.getRealParameterTypes();
    
    // Prepare list of input parameters
    BPLVariable[] inParams = new BPLVariable[paramTypes.length];
    //@deprecated inParams[0] = new BPLVariable(PRE_HEAP_VAR, new BPLTypeName(HEAP_TYPE));
    for (int i = 0; i < inParams.length; i++) {
      BPLBuiltInType bplType = type(paramTypes[i]);
      inParams[i] = new BPLVariable(paramVar(i), bplType);
    }

    // Prepare list of output parameters
    // BPLVariable[] outParams = BPLVariable.EMPTY_ARRAY;
    List<BPLVariable> outParams = new ArrayList<BPLVariable>();
    //@deprecated outParams.add(new BPLVariable(RETURN_HEAP_PARAM, new BPLTypeName(HEAP_TYPE)));
    outParams.add(new BPLVariable(RETURN_STATE_PARAM, new BPLTypeName(RETURN_STATE_TYPE)));
    if (provideReturnValue) {
      if (method.isConstructor()) {
        outParams.add(new BPLVariable(RESULT_PARAM, BPLBuiltInType.REF));
      } else {
        outParams.add(new BPLVariable(RESULT_PARAM, type(method.getReturnType())));
      }
    }
    outParams.add(new BPLVariable(EXCEPTION_PARAM, BPLBuiltInType.REF));

    BPLImplementation implementation = new BPLImplementation(
        name,
        inParams,
        outParams.toArray(new BPLVariable[outParams.size()]),
        body);

    BPLSpecification spec = new BPLSpecification(
        getRequiresClauses(),
        new BPLModifiesClause[] {
            translateModifiesClause(method, getInParameters())
        }, /* getModifiesClauses(), */
        getEnsuresClauses()
    );
    
    //System.out.println("[" + method.getName() + "]  " + translateMethodFrame(method, getInParameters()).toString());
    printSpecification(spec);

    return new BPLProcedure(
        name,
        inParams,
        outParams.toArray(new BPLVariable[outParams.size()]), spec, implementation
    );
  }

  
  private void printSpecification(BPLSpecification spec) {
    System.out.println("Specification for " + method.getQualifiedName());
    for (BPLSpecificationClause clause : spec.getClauses()) {
      // TODO
      System.out.println("\t" + clause.toString());
    }
  }
  

  /**
   * TODO: not yet finished
   * 
   * @return BPLRequiresClause declaring the precondition of the current
   *         procedure.
   */
  private BPLRequiresClause[] getRequiresClauses() {

    List<BPLRequiresClause> requiresClauses = new ArrayList<BPLRequiresClause>();
    JType[] params = method.getRealParameterTypes();

    // If we have a this object, then it is not null.
    boolean hasThisParameter = !method.isStatic() && !method.isConstructor();
    
    if (hasThisParameter) {
      requiresClauses.add(new BPLRequiresClause(notEqual(
          var(thisVar()),
          BPLNullLiteral.NULL
      )));
      requiresClauses.add(new BPLRequiresClause(alive(
          rval(var(thisVar())),
          var(HEAP_VAR)
      )));
      requiresClauses.add(new BPLRequiresClause(isOfType(
          rval(var(thisVar())),
          typeRef(params[0])
      )));
    }

    // For every method parameter, we do the following:
    // - assume its type is a subtype of the static type
    // - assume the parameter's value is alive
    // - assign the parameter to the corresponding local variable in the stack
    // frame
    for (int i = (hasThisParameter ? 1 : 0); i < params.length; i++) {
      BPLExpression typeRef = typeRef(params[i]);
      if (params[i].isBaseType()) {
        // Base type: There is no need to assume aliveness of base types.
        requiresClauses.add(new BPLRequiresClause(isOfType(
            ival(var(paramVar(i))),
            typeRef)));
      } else {
        if (!method.isConstructor()) {
        requiresClauses.add(new BPLRequiresClause(alive(
            rval(var(paramVar(i))),
            var(HEAP_VAR))));
        requiresClauses.add(new BPLRequiresClause(isOfType(
            rval(var(paramVar(i))),
            typeRef)));
        }
      }
      // addAssignment(var(localVar(i, params[i])), var(paramVar(i)));
    }

    // Special handling for constructors.
    if (method.isConstructor()) {
      // The JVM guarantees us that the this object is not aliased at the
      // beginning of a constructor, so let's assume that.

      // No parameter is equal to the this object.
      for (int i = 1; i < params.length; i++) {
        // We only insert the appropriate assumption for types which are
        // compatible to the type of the this object since other assumptions are
        // redundant.
        if (method.getOwner().isSubtypeOf(params[i]) || params[i].isSubtypeOf(method.getOwner())) {
          requiresClauses.add(new BPLRequiresClause(notEqual(
              var(thisVar()),
              var(paramVar(i))
          )));
        }
      }

      // No object in the heap is equal to the this object.
      /* TODO revise the following two requirements
      String l = quantVarName("l");
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      requiresClauses.add(new BPLRequiresClause(forall(lVar, notEqual(
          rval(var(thisVar())),
          get(var(HEAP_VAR), var(l))))));

      // Initialize the fields of the this object to their default values.
      String f = quantVarName("f");
      BPLVariable fVar = new BPLVariable(f, BPLBuiltInType.NAME);
      requiresClauses.add(new BPLRequiresClause(forall(fVar, isEqual(get(
          var(HEAP_VAR),
          fieldLoc(var(thisVar()), var(f))), initVal(fieldType(var(f)))))));
      */
    }


    // Assume the appropriate invariants if it is not a constructor.
    if (!method.isConstructor()) {
      requiresClauses.add(requireAllInvariants(method.isConstructor()));
    }
    
    // Assume the method's effective precondition.
    requiresClauses.add(new BPLRequiresClause(translatePrecondition(
        method,
        getInParameters())));

    /*
     * if (!method.isStatic()) {
     *   BPLExpression this_type = typeRef(method.getOwner());
     *   BPLExpression this_not_null = notEqual(rval(var(thisVar())), BPLNullLiteral.NULL);
     *   BPLExpression this_has_correct_type = isSubtype(typ(rval(var(thisVar()))), this_type);
     *   // TODO: C == type of "this" object
     *   result = logicalAnd(result, this_not_null, this_has_correct_type);
     * }
     */

    return requiresClauses.toArray(new BPLRequiresClause[requiresClauses.size()]);
  }

  /**
   * TODO
   * 
   * @return BPLMeasureClauses declaring global variables that are modifies in
   *         the procedure.
   * @deprecated
   */
  private BPLModifiesClause[] getModifiesClauses() {

    return null;
    
    /*
    List<BPLModifiesClause> modifiesClauses = new ArrayList<BPLModifiesClause>();

    // TODO read modified variables from BPL file
    translateModifiesClause(method, get)
    
    modifiesClauses.add(new BPLModifiesClause(var(HEAP_VAR)));

    return modifiesClauses.toArray(new BPLModifiesClause[modifiesClauses.size()]);
    */
  }


  /**
   * TODO incomplete
   * 
   * @return BPLEnsuresClause List of ensures-clauses declaring the postcondition
   *         of the current procedure.
   */
  private BPLEnsuresClause[] getEnsuresClauses() {

    List<BPLEnsuresClause> ensuresClauses = new ArrayList<BPLEnsuresClause>();

    // TODO
    // ensures (forall v: Value    :: alive(v, old(heap)) ==> alive(v, heap));
    // ensures (forall l: Location :: l != fieldLoc(param0, Account.balance) ==> get(heap, l) == get(old(heap), l));

    // Prepare precondition (for only the preconditions implies the postcondition)
    BPLExpression P = translatePrecondition(
        method,
        getInParameters()
    );
    
    // Assert the effective normal postcondition and the method frame of the method.
    BPLExpression Q = translatePostcondition(
        method,
        RESULT_VAR,
        getInParameters()
    );
    /* 
    BPLExpression Q = logicalAnd(
        translateMethodFrame(
            method,
            getInParameters()
        ),
        translatePostcondition(
            method,
            / * HEAP_VAR, * /
            RESULT_VAR,
            getInParameters()
        )
    ); */

    BPLExpression FC = translateMethodFrame(
        method,
        getInParameters()
    );
    
    // If no method specifications are provided,
    // establish default frame condition
    if (FC == null) {
      String r = quantVarName("r");
      BPLVariable ref = new BPLVariable(r, BPLBuiltInType.REF);
      FC = forall(
          ref,
          implies(
              alive(rval(var(r)), old(var(HEAP_VAR))),
              logicalAnd(
                  isEqual(
                      get(var(HEAP_VAR), fieldLoc(var(r), typ(rval(var(r))))),
                      get(old(var(HEAP_VAR)), fieldLoc(var(r), typ(rval(var(r)))))
                  ),
                  alive(rval(var(r)), var(HEAP_VAR))
              )
          )
      );
    }
   
    boolean provideReturnValue = !method.isVoid() || method.isConstructor();

    // Ensure normal postcondition
    BPLExpression condition = isNormalReturnState(var(RETURN_STATE_PARAM));
    BPLExpression q = BPLBoolLiteral.TRUE;
    
    if (method.isConstructor()) {
      q = logicalAnd(
            Q,
            notEqual(var(RESULT_PARAM), BPLNullLiteral.NULL),
            alive(rval(var(RESULT_PARAM)), var(HEAP_VAR)),
            isOfType(rval(var(RESULT_PARAM)), typeRef(method.getOwner()))
      );
    } else {
      if (provideReturnValue) {
        if (method.getReturnType().isReferenceType()) {
          // The method's return value is a reference type (ref)
          q = logicalAnd(
            // isNormalReturnState(var(RETURN_STATE_PARAM)),
            alive(rval(var(RESULT_PARAM)), var(HEAP_VAR)),
            isOfType(rval(var(RESULT_PARAM)), typeRef(method.getReturnType())));
        } else {
          // The method's return value is not a reference type
          // (in this particular case, we assume type int)
          q = logicalAnd(
            // isNormalReturnState(var(RETURN_STATE_PARAM)),
            alive(ival(var(RESULT_PARAM)), var(HEAP_VAR)),
            isOfType(ival(var(RESULT_PARAM)), typeRef(method.getReturnType())));
        }
      }
    }

    // Add postcondition for normal method termination
    ensuresClauses.add(new BPLEnsuresClause(
        implies(
            P,
            implies(condition, logicalAnd(q, FC))
        )
    ));

    // Handle the different exceptional terminations of the method.
    JClassType[] exceptions = method.getExceptionTypes();
    for (JClassType exception : exceptions) {
      
      // addAssume(isInstanceOf(rval(var(refStackVar(0))), typeRef(exception)));

      BPLExpression Qex = translateXPostcondition(
          method,
          exception,
          refStackVar(0),
          getInParameters()
      );

      BPLExpression ex_condition = logicalAnd(
          isExceptionalReturnState(var(RETURN_STATE_PARAM)),
          isOfType(rval(var(EXCEPTION_PARAM)), typeRef(exception))
      );
      BPLExpression qex =  logicalAnd(Qex,
          alive(rval(var(EXCEPTION_PARAM)), var(HEAP_VAR))
      );
      
      // Add exceptional postcondition for this particular exception
      ensuresClauses.add(new BPLEnsuresClause(
          implies(
              P,
              implies(
                  ex_condition,
                  qex
              )
          )
      ));
    }

    if (Main.getProject().simplifyLogicalExpressions()) {
      for (int i = ensuresClauses.size() - 1; i >= 0; i--) {
        if (ensuresClauses.get(i).getExpression() == BPLBoolLiteral.TRUE) {
          ensuresClauses.remove(i);
        }
      }
    }
    
    // Ensure exposed (object) invariants
    ensuresClauses.add(ensureExposedInvariants(false));
    
    return ensuresClauses.toArray(new BPLEnsuresClause[ensuresClauses.size()]);
  }


  /**
   * Filters only variable declarations for variables which actually appear in
   * the procedure implementation.
   * 
   * @param blocks List of blocks of the current procedure.
   * @param vars List of BPLVariables which might be used in this procedure.
   * @return BPLVariableDeclaration declaring all variables which actually
   *         appear in the implementation.
   */
  private BPLVariableDeclaration filterVariableDeclarations(
      List<BPLBasicBlock> blocks,
      BPLVariable... vars) {
    List<BPLVariable> new_vars = new ArrayList<BPLVariable>();
    for (BPLBasicBlock block : blocks) {
      for (BPLCommand command : block.getCommands()) {
        for (BPLVariable var : vars) {
          if (command.toString().contains(var.getName())
              && !new_vars.contains(var)) {
            new_vars.add(var);
          }
        }
      }
    }
    return new BPLVariableDeclaration(new_vars.toArray(new BPLVariable[new_vars
        .size()]));
  }


  /**
   * Returns the name to use for the BoogiePL procedure resulting from the
   * translation of the given bytecode {@code method}. The returned string is a
   * valid BoogiePL identifier and it is guaranteed to be different from the
   * procedure name returned for any different method (including overloaded
   * methods).
   * 
   * @param method The bytecode method for which to return the BoogiePL
   *          procedure name.
   * @return The BoogiePL procedure name.
   */
  private String getProcedureName(BCMethod method) {
    String name;

    // The names of constructors and class initializers used in the JVM are not
    // valid BoogiePL identifiers, so we give them different names which may
    // not clash with names of ordinary methods.
    if (method.isConstructor()) {
      name = method.getOwner().getName() + "." + CONSTRUCTOR_NAME;
    } else if (method.isClassInitializer()) {
      name = method.getOwner().getName() + "." + CLASS_INITIALIZER_NAME;
    } else {
      name = method.getQualifiedName();
    }

    // Append the names of the method's parameters in order to correctly handle
    // overloaded methods.
    for (JType type : method.getParameterTypes()) {
      name += ".";
      if (type.isArrayType()) {
        // For array types, we append the array's component type name followed
        // by the array's dimension.
        JArrayType arrayType = (JArrayType)type;
        JType componentType = arrayType.getComponentType();
        name += componentType.getName() + "#" + arrayType.getDimension();
      } else {
        name += type.getName();
      }
    }

    return name;
  }

  /**
   * Convenience method returning the names of the in-parameter names of the
   * BoogiePL procedure being generated.
   * 
   * @return The names of the procedure's in-parameters.
   */
  private String[] getInParameters() {
    JType[] paramTypes = method.getRealParameterTypes();
    String[] params = new String[paramTypes.length];
    for (int i = 0; i < params.length; i++) {
      params[i] = paramVar(i);
    }
    return params;
  }

  /**
   * Generates a set of assumptions justified by the JVM and its type system. In
   * addition, the initialization of the first stack frame of the method is
   * translated to BoogiePL. The information assumed at this point and
   * guaranteed by the JVM includes the following:
   * <ul>
   * <li> The this object, if any, is never {@code null}. </li>
   * <li> The types of the parameter values are subtypes of their static types
   * and all reachable values are alive. </li>
   * <li> If we are inside a constructor, the this object is not aliased and its
   * instance fields are initialized by their default values. </li>
   * </ul>
   */
  private void translateInit() {
    startBlock(INIT_BLOCK_LABEL);

    callStatements = 0; // count the number of call statements used so far

    /*
     * // Keep a copy of the method's pre-state heap.
     * addAssignment(var(OLD_HEAP_VAR), var(HEAP_VAR));
     *  // If we have a this object, then it is not null. if
     * (!method.isStatic()) { addAssume(nonNull(var(thisVar()))); }
     *  // For every method parameter, we do the following: // - assume its type
     * is a subtype of the static type // - assume the parameter's value is
     * alive // - assign the parameter to the corresponding local variable in
     * the stack // frame JType[] params = method.getRealParameterTypes(); for
     * (int i = 0; i < params.length; i++) { BPLExpression typeRef =
     * typeRef(params[i]); if (params[i].isBaseType()) { // There is no need to
     * assume aliveness of value types.
     * addAssume(isOfType(ival(var(paramVar(i))), typeRef)); } else {
     * addAssume(alive(rval(var(paramVar(i))), var(HEAP_VAR)));
     * addAssume(isOfType(rval(var(paramVar(i))), typeRef)); }
     * addAssignment(var(localVar(i, params[i])), var(paramVar(i))); }
     *  // Special handling for constructors. if (method.isConstructor()) { //
     * The JVM guarantees us that the this object is not aliased at the //
     * beginning of a constructor, so let's assume that.
     *  // No parameter is equal to the this object. for (int i = 1; i <
     * params.length; i++) { // We only insert the appropriate assumption for
     * types which are // compatible to the type of the this object since other
     * assumptions are // redundant. if
     * (method.getOwner().isSubtypeOf(params[i]) ||
     * params[i].isSubtypeOf(method.getOwner())) {
     * addAssume(notEqual(var(thisVar()), var(paramVar(i)))); } }
     *  // No object in the heap is equal to the this object. String l =
     * quantVarName("l"); BPLVariable lVar = new BPLVariable(l, new
     * BPLTypeName(LOCATION_TYPE)); addAssume(forall( lVar,
     * notEqual(rval(var(thisVar())), get(var(HEAP_VAR), var(l)))));
     *  // Initialize the fields of the this object to their default values.
     * String f = quantVarName("f"); BPLVariable fVar = new BPLVariable(f,
     * BPLBuiltInType.NAME); addAssume(forall( fVar, isEqual( get(var(HEAP_VAR),
     * fieldLoc(var(thisVar()), var(f))), initVal(fieldType(var(f)))))); }
     * 
     * endBlock(PRE_BLOCK_LABEL);
     */
    
    // Assume the appropriate invariants.
    assumeAllInvariants(method.isConstructor());

    // Assume the method's effective precondition.
    addAssume(translatePrecondition(method, getInParameters()));


    //@deprecated addAssume(notEqual(var(thisVar()), BPLNullLiteral.NULL));
    //@deprecated addAssume(alive(rval(var(thisVar())), var(HEAP_VAR)));

    JType[] params = method.getRealParameterTypes();
    for (int i = 0; i < params.length; i++) {
      addAssignment(var(localVar(i, params[i])), var(paramVar(i)));
    }

    //@deprecated addAssignment(var(HEAP_VAR), var(PRE_HEAP_VAR));
    
    // requires param0 != null;
    // requires alive(rval(param0), heap);

    endBlock(method.getCFG().getEntryBlock().outEdgeIterator().next());
  }

  /**
   * Initializes the internal state of the translator. Should be called whenever
   * a new bytecode method is translated.
   */
  private void initTranslation() {
    blockLabel = null;
    commands = null;
    blocks = new ArrayList<BPLBasicBlock>();
    loopHeapVars = new LinkedHashMap<BasicBlock, String>();
    loopVariantVars = new LinkedHashMap<BMLLoopVariant, String>();
  }

  /**
   * Generates a set of assumptions justified by the verification methodology
   * employed. In particular, the following is assumed at the beginning of the
   * method:
   * <ul>
   * <li> The invariants of all objects, eventually excluding the this object in
   * case we are inside a constructor. </li>
   * <li> The method's effective precondition. </li>
   * </ul>
   * @deprecated
   */
  private void translatePre() {
    startBlock(PRE_BLOCK_LABEL);

    // Assume the appropriate invariants.
    assumeAllInvariants(method.isConstructor());

    // Assume the method's effective precondition.
    addAssume(translatePrecondition(method, getInParameters()));

    endBlock(method.getCFG().getEntryBlock().outEdgeIterator().next());
  }

  /**
   * Generates a set of assertions for normal as well as exceptional
   * terminations of the method being translated in order to enforce the desired
   * verification methodology. In particular, the following assertions need to
   * be satisfied when the method terminates:
   * <ul>
   * <li> The method's effective (exceptional) postcondition must hold. </li>
   * <li> The invariants of the method's receiver type must hold for all
   * relevant objects, even if the method terminates with an exception. </li>
   * <li> The method's frame condition must hold, even if the method terminates
   * with an exception. </li>
   * </ul>
   */
  private void translatePost() {

    startBlock(EXCEPTION_HANDLERS_LABEL);

    /*
     * // Handle the normal termination of the method.
     * startBlock(POST_BLOCK_LABEL);
     *  // Assert the effective normal postcondition of the method. // TODO[sw]:
     * remove this check and insert appropriate "ensures" clause in the //
     * procedure declaration addAssert(translatePostcondition( method,
     * OLD_HEAP_VAR, RESULT_VAR, getInParameters()));
     * endBlock(EXIT_BLOCK_LABEL);
     */

    // Handle the different exceptional terminations of the method.
    JClassType[] exceptions = method.getExceptionTypes();
    for (JClassType exception : exceptions) {
      startBlock(postXBlockLabel(exception));

      // addAssume(isInstanceOf(rval(var(refStackVar(0))), typeRef(exception)));
      addAssume(isInstanceOf(rval(var(EXCEPTION_PARAM)), typeRef(exception)));

      /*
       * REMOVE: exceptional postconditions are checked implicitely by Boogie
       * addAssert(translateXPostcondition( method, exception, OLD_HEAP_VAR,
       * refStackVar(0), getInParameters()));
       */
      endBlock(EXIT_BLOCK_LABEL);
    }

    // The exit block contains all the verification conditions which must hold
    // even if the method terminates with an exception, namely:
    // - the invariants of the relevant objects
    // - the method's frame condition
    startBlock(EXIT_BLOCK_LABEL);

    /*
     * assertExposedInvariants(false);
     *  // Assert the method's frame condition.
     * addAssert(translateMethodFrame(method, OLD_HEAP_VAR, getInParameters()));
     */
    
    //@deprecated addAssignment(var(RETURN_HEAP_PARAM), var(HEAP_VAR));
    
    boolean provideReturnValue = !method.isVoid() || method.isConstructor();
    
    if (provideReturnValue) {
      
      JType retType = method.isConstructor()
        ? method.getOwner()
        : method.getReturnType();
      
      BPLExpression topElem = var(stackVar(0, retType));
      
      if (method.getReturnType().isReferenceType() || method.isConstructor()) {
        addAssume(notEqual(topElem, BPLNullLiteral.NULL));
        addAssume(alive(rval(topElem), var(HEAP_VAR)));
      } else {
        addAssume(alive(ival(topElem), var(HEAP_VAR)));
      }
      addAssignment(var(RESULT_PARAM), var(stackVar(0, retType)));
      addAssignment(var(RETURN_STATE_PARAM), var(NORMAL_RETURN_STATE));
      
    }

    endBlock();
  }

  /**
   * Translates the method's bytecode instructions along with all the local BML
   * annotations (assertions, loop specifications, ...). The translation of the
   * program flow follows the method's control flow graph.
   */
  private void translateInstructions() {
    InstructionTranslator insnTranslator = new InstructionTranslator();
    ControlFlowGraph cfg = method.getCFG();
    Iterator<BasicBlock> cfgBlocks = cfg.blockIterator();
    while (cfgBlocks.hasNext()) {
      BasicBlock cfgBlock = cfgBlocks.next();
      // Filter out the synthetic entry and exit blocks from the control flow
      // graph.
      if (!cfg.isSyntheticBlock(cfgBlock)) {
        translateCFGBlockStart(cfgBlock);
        // Let the instruction translator know which is the current basic block
        // in the control flow graph.
        insnTranslator.cfgBlock = cfgBlock;
        Iterator<InstructionHandle> insns = cfgBlock.instructionIterator();
        while (insns.hasNext()) {
          InstructionHandle insn = insns.next();
          // Translate local annotations such as assertions and assumptions.
          // Note that loop specifications are not translated here as they may
          // only appear at the beginning of a basic block in the control flow
          // graph and not at any arbitrary instruction.
          // FIXME the following method generates assertions that are not
          //       explicitely specified in the BML file.
          // translateInstructionAnnotations(insn);
          // Let the instruction translator know which is the current
          // instruction handle before doing the actual translation.
          insnTranslator.handle = insn;
          insn.accept(insnTranslator);
        }

        // If we are still inside a BoogiePL block after having translated all
        // the instructions inside a basic block of the control flow graph, we
        // must have a fall through edge in the control flow graph which is not
        // translated by the individual instructions but here instead.
        if (isInsideBlock()) {
          InstructionHandle nextInsn = cfgBlock.getLastInstruction().getNext();
          BasicBlock nextBlock = method.getCFG().findBlockStartingAt(nextInsn);
          Edge fallThroughEdge = cfgBlock.getSuccessorEdge(nextBlock);
          endBlock(fallThroughEdge);
        }
      }
    }
  }

  /**
   * Assumes all invariants of all objects, eventually excluding the
   * {@code this} object.
   * 
   * @param excludeThisObject Whether to exclude the {@code this} object from
   *          the set of objects on which the invariants are assumed.
   */
  private void assumeAllInvariants(boolean excludeThisObject) {
    // TODO
    /*
    String t = quantVarName("t");
    String o = quantVarName("o");
    BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
    BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
    if (excludeThisObject) {
      // Assume all invariants of all objects but the this object.
      addAssume(forall(tVar, oVar, implies(
          notEqual(var(o), var(thisVar())),
          inv(var(t), var(o), var(HEAP_VAR)))));
    } else {
      // Assume all invariants of all objects.
      addAssume(forall(tVar, oVar, inv(var(t), var(o), var(HEAP_VAR))));
    }
    */
  }

  private BPLRequiresClause requireAllInvariants(boolean excludeThisObject) {
    // TODO
    String t = quantVarName("t");
    String o = quantVarName("o");
    BPLVariable tVar = new BPLVariable(t, BPLBuiltInType.NAME);
    BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
    if (excludeThisObject) {
      // Assume all invariants of all objects but the this object.
      return new BPLRequiresClause(forall(tVar, oVar, implies(notEqual(
          var(o),
          var(thisVar())), inv(var(t), var(o), var(HEAP_VAR)))));
    } else {
      // Assume all invariants of all objects.
      return new BPLRequiresClause(forall(tVar, oVar, inv(
          var(t),
          var(o),
          var(HEAP_VAR))));
    }
  }

  /**
   * Generates proof obligations for verifying the invariants of all the objects
   * which are considered to be exposed, meaning that their invariants may have
   * been broken.
   * 
   * @param excludeThisObject Whether to exclude the {@code this} object from
   *          the set of objects on which the invariants are checked.
   */
  /*
  private void assertExposedInvariants(boolean excludeThisObject) {
    BPLExpression type = typeRef(method.getOwner());
    if (project.isThisInvariantsOnly()) {
      if (!method.isStatic() && !excludeThisObject) {
        addAssert(inv(type, var(thisVar()), var(HEAP_VAR)));
      }
    } else {
      String o = quantVarName("o");
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      if (excludeThisObject) {
        addAssert(forall(oVar,
            implies(
              notEqual(var(o), var(thisVar())),
              inv(
                type,
                var(o),
                var(HEAP_VAR)
              )
            )
        ));
      } else {
        addAssert(forall(oVar, inv(type, var(o), var(HEAP_VAR))));
      }
    }
  }
*/

  private BPLEnsuresClause ensureExposedInvariants(boolean excludeThisObject) {
    BPLExpression type = typeRef(method.getOwner());
    if (project.isThisInvariantsOnly()) {
      if (!method.isStatic() && !excludeThisObject) {
        return new BPLEnsuresClause(inv(type, var(thisVar()), var(HEAP_VAR)));
      } else {
        return new BPLEnsuresClause(BPLBoolLiteral.TRUE); // TODO: return TRUE or FALSE ?
      }
    } else {
      String o = quantVarName("o");
      BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
      if (excludeThisObject) {
        return new BPLEnsuresClause(forall(oVar, implies(notEqual(
            var(o),
            var(thisVar())), inv(type, var(o), var(HEAP_VAR)))));
      } else {
        return new BPLEnsuresClause(forall(oVar, inv(
            type,
            var(o),
            var(HEAP_VAR))));
      }
    }
  }

  /**
   * Translates the local BML annotations (assertions, assumptions, ...)
   * attached to the given instruction.
   * 
   * @param insn The instruction handle at which to translate the local BML
   *          annotations.
   */
  /*
  private void translateInstructionAnnotations(InstructionHandle insn) {
    for (BMLAssertStatement assertion : insn.getAssertions()) {
      addAssert(translateLocalSpecification(assertion.getPredicate(), insn));
    }
    for (BMLAssumeStatement assumption : insn.getAssumptions()) {
      addAssume(translateLocalSpecification(assumption.getPredicate(), insn));
    }
  }
  */

  /**
   * Translates the start of a new basic block in the method's control flow
   * graph. Beside starting a new BoogiePL block, this method also handles the
   * translation of loop headers by inserting all the loop invariants resulting
   * from BML specifications (loop specifications) but also from the
   * verification methodology itself.
   * 
   * @param cfgBlock The basic block of the method's control flow graph to
   *          start.
   */
  private void translateCFGBlockStart(BasicBlock cfgBlock) {
    startBlock(blockLabel(cfgBlock));

    // Check whether the new basic block is a loop header.
    if (cfgBlock.isBackEdgeTarget()) {
      InstructionHandle insn = cfgBlock.getFirstInstruction();

      // Assume the type information contained in the loop headers stack frame
      // in order to preserve that information for potential loop targets.
      StackFrame frame = insn.getFrame();

      // Assume the type information of the local variables.
      // Assume the type information of the local variables.
      for (int i = 0; i < frame.getLocalCount(); i++) {
        JType type = frame.getLocal(i);
        if (type != null) {
          if (type.isBaseType()) {
            addAssume(isOfType(ival(var(localVar(i, type))), typeRef(type)));
          } else if (type != JNullType.NULL) {
            addAssume(isOfType(rval(var(localVar(i, type))), typeRef(type)));
          }
        }
      }
      // Assume the type information of the stack variables.
      for (int i = 0; i < frame.getStackSize(); i++) {
        JType type = frame.peek(i);
        if (type != null) {
          if (type.isBaseType()) {
            addAssume(isOfType(ival(var(stackVar(i, type))), typeRef(type)));
          } else if (type != JNullType.NULL) {
            addAssume(isOfType(rval(var(stackVar(i, type))), typeRef(type)));
          }
        }
      }

      // Assume that objects allocated at the loop entry remain allocated inside
      // the loop. Note that this assumption ignores the effect of any potential
      // garbage collector de-allocating objects inside the loop.
      String loopHeap = getLoopHeapVar(cfgBlock);
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAssume(forall(vVar, implies(alive(var(v), var(loopHeap)), alive(
          var(v),
          var(HEAP_VAR)))));

      // If we are verifying the invariants on all objects of the method's
      // receiver type (and not only on the this object), we must enforce that
      // the invariants of objects of that type allocated inside the loop
      // satisfy their invariants at each loop iteration. This is a necessary
      // restriction since in a sound verification of loops we usually have
      // no information about the state of objects allocated inside the loop
      // when leaving the loop, meaning that if we do not verify their
      // invariants at this point, we could not verify them anymore. Note that
      // this statement is also true to some extent for objects which were
      // already allocated when entering the loop but their state can be
      // maintained through loop iterations by explicitly specifying loop
      // invariants in BML while objects allocated inside the loop cannot be
      // referred to in such explicit invariants. Therefore, we insert the
      // following implicit invariant of the verification methodology which
      // ensures that the invariants of objects allocated inside the loop hold
      // at every loop iteration.
      // ... end of comment ;) ...
      if (!project.isThisInvariantsOnly()) {
        String o = quantVarName("o");
        BPLVariable oVar = new BPLVariable(o, BPLBuiltInType.REF);
        addAssert(forall(oVar,
            implies(
              logicalNot(alive(
                rval(var(o)),
                var(loopHeap)
              )), 
              inv(
                typeRef(method.getOwner()),
                var(o),
                var(HEAP_VAR)
              )
            )
        ));
      }

      // Translate all the loop specifications.
      // FIXME[om]: Should probably merge loop frame conditions!
      for (BMLLoopSpecification loopSpec : getLoopSpecificationsAt(cfgBlock)) {
        // Assert the loop invariant itself.
        addAssert(translateLoopInvariant(loopSpec.getInvariant(), insn));

        BMLLoopVariant variant = loopSpec.getVariant();
        String variantVar = getLoopVariantVar(variant);
        // Assert the non-negativity of loop variant expressions.
        addAssert(lessEqual(intLiteral(0), translateLoopVariant(variant, insn)));

        // Assert the loop modifies clause.
        addAssert(translateLoopFrame(loopSpec.getModifies(), insn));

        // Remember the value of the loop variant expression at the beginning
        // of the loop. This value will be used at the back edges of this loop
        // in order to check that the loop variant expression indeed decreases
        // a each iteration.
        addAssignment(var(variantVar), translateLoopVariant(variant, insn));
      }
    }
  }

  private List<BMLLoopSpecification> getLoopSpecificationsAt(BasicBlock cfgBlock) {
    List<BMLLoopSpecification> specs = new ArrayList<BMLLoopSpecification>();
    Iterator<Edge> inEdges = cfgBlock.inEdgeIterator();
    specs.addAll(cfgBlock.getFirstInstruction().getLoopSpecifications());
    while (inEdges.hasNext()) {
      Edge inEdge = inEdges.next();
      if (inEdge.isBackEdge()) {
        InstructionHandle lastInsn = inEdge.getSource().getLastInstruction();
        specs.addAll(lastInsn.getLoopSpecifications());
      }
    }
    return specs;
  }

  /**
   * Translates the {@code method}'s effective precondition.
   * 
   * @param method The method whose precondition should be translated.
   * @param parameters The names of the method's parameters.
   * @return A BoogiePL predicate expressing the method's effective
   *         precondition.
   */
  private BPLExpression translatePrecondition(
      BCMethod method,
      String[] parameters) {
    SpecificationTranslator translator = SpecificationTranslator.forPrecondition(HEAP_VAR, parameters);
    return translator.translate(context, project.getSpecificationDesugarer().getPrecondition(method));
  }
  
  /**
   * Translates the {@code method}'s effective modified variables.
   * 
   * @param method The method whose modifies variables should be translated.
   * @return A BoogiePL predicate expressing the method's effective
   *         modified variables.
   */
  private BPLModifiesClause translateModifiesClause(
      BCMethod method,
      String[] parameters) {
    SpecificationTranslator translator = SpecificationTranslator.forModifiesClause(HEAP_VAR, parameters);
    return translator.translateModifiesStoreRefs(context, project.getSpecificationDesugarer().getModifiesStoreRefs(method));
  }

  /**
   * Translates the {@code method}'s effective normal postcondition.
   * 
   * @param method The method whose normal postcondition should be translated.
   * @param oldHeap The name of the method's pre-state heap.
   * @param result The name of the method's return value.
   * @param parameters The names of the method's parameters.
   * @return A BoogiePL predicate expressing the method's effective normal
   *         postcondition.
   */
  private BPLExpression translatePostcondition(
      BCMethod method,
      /*String oldHeap,*/
      String result,
      String[] parameters) {
    SpecificationTranslator translator = SpecificationTranslator.forPostcondition(HEAP_VAR, /* oldHeap, */ result, parameters);
    return translator.translate(context, project.getSpecificationDesugarer().getPostcondition(method));
  }

  /**
   * Translates the {@code method}'s effective exceptional postcondition.
   * 
   * @param method The method whose exceptional postcondition should be
   *          translated.
   * @param exception The exception type thrown.
   * @param oldHeap The name of the method's pre-state heap.
   * @param exceptionObject The name of the exception object thrown.
   * @param parameters The names of the method's parameters.
   * @return A BoogiePL predicate expressing the method's effective exceptional
   *         postcondition.
   */
  private BPLExpression translateXPostcondition(
      BCMethod method,
      JType exception,
      /* String oldHeap, */
      String exceptionObject,
      String[] parameters) {
    SpecificationTranslator translator = SpecificationTranslator.forPostcondition(HEAP_VAR, /* oldHeap, */ exceptionObject, parameters);
    return translator.translate(context, project.getSpecificationDesugarer().getExceptionalPostcondition(method, exception));
  }

  /**
   * Convenience method which returns the names of the local variables in the
   * stack frame of the given bytecode instruction.
   * 
   * @param insn The instruction for which to return the names of the stack
   *          frame's local variables.
   * @return The names of the stack frame's local variables.
   */
  private static String[] getLocalVariablesAt(InstructionHandle insn) {
    StackFrame frame = insn.getFrame();
    String[] localVariables = new String[frame.getLocalCount()];
    for (int i = 0; i < localVariables.length; i++) {
      if (frame.getLocal(i) != null) {
        localVariables[i] = localVar(i, frame.getLocal(i));
      }
    }
    return localVariables;
  }

  /**
   * Convenience method which returns the names of the stack variables in the
   * stack frame of the given bytecode instruction.
   * 
   * @param insn The instruction for which to return the names of the stack
   *          frame's stack variables.
   * @return The names of the stack frame's stack variables.
   */
  private static String[] getStackVariablesAt(InstructionHandle insn) {
    StackFrame frame = insn.getFrame();
    String[] stackVariables = new String[frame.getStackSize()];
    for (int i = 0; i < stackVariables.length; i++) {
      if (frame.peek(i) != null) {
        stackVariables[i] = stackVar(i, frame.peek(i));
      }
    }
    return stackVariables;
  }

  /**
   * Translates the local BML expression (assertion, loop specification, ...) at
   * the given instruction.
   * 
   * @param expression The local BML expression to translate.
   * @param insn The instruction handle to which the BML annotation belongs.
   * @return The BML annotation translated to BoogiePL.
   */
  private BPLExpression translateLocalSpecification(
      BMLExpression expression,
      InstructionHandle insn) {
    SpecificationTranslator translator = SpecificationTranslator
        .forLocalSpecification(
            HEAP_VAR,
            PRE_HEAP_VAR,
            getLocalVariablesAt(insn),
            getStackVariablesAt(insn),
            getInParameters());
    return translator.translate(context, expression);
  }

  private BPLExpression translateLoopInvariant(
      BMLLoopInvariant invariant,
      InstructionHandle loopHead) {
    return translateLocalSpecification(invariant.getPredicate(), loopHead);
  }

  private BPLExpression translateLoopVariant(
      BMLLoopVariant variant,
      InstructionHandle loopHead) {
    return translateLocalSpecification(variant.getExpression(), loopHead);
  }

  public BPLExpression translateMethodFrame(
      BCMethod method,
      String[] parameters) {
    List<BPLExpression> expr = new ArrayList<BPLExpression>();
    List<BCMethod> overrides = method.getOverrides();
    for (BCMethod override : overrides) {
      BMLMethodSpecification spec = override.getSpecification();
      if (spec != null) {
        BMLSpecificationCase[] specCases = spec.getCases();
        for (int i = 0; i < specCases.length; i++) {
          BMLStoreRef[] storeRefs = specCases[i].getModifies().getStoreRefs();
          BMLExpression requires;
          if (specCases.length == 1) {
            requires = spec.getRequires().getPredicate();
          } else {
            requires = specCases[i].getRequires().getPredicate();
          }
          expr.add(translateMethodFrame(
              requires,
              storeRefs,
              parameters));
        }
      }
    }
    if (expr.size() > 0) {
      return logicalAnd(expr.toArray(new BPLExpression[expr.size()]));
    } else {
      return BPLBoolLiteral.TRUE;
    }
  }

  private BPLExpression translateMethodFrame(
      BMLExpression requires,
      BMLStoreRef[] storeRefs,
      String[] parameters) {
    if (storeRefs.length > 0) {
      String l = quantVarName("l");
      ModifiesFilter filter = ModifiesFilter.forMethod(old(var(HEAP_VAR)).toString(), parameters, l);
      BPLExpression expr = filter.translate(context, storeRefs);
      expr = logicalAnd(alive(rval(obj(var(l))), old(var(HEAP_VAR))), expr);
      BPLExpression left = get(var(HEAP_VAR), var(l));
      BPLExpression right = get(old(var(HEAP_VAR)), var(l));
      expr = implies(expr, isEqual(left, right));
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      expr = forall(lVar, expr);
      SpecificationTranslator translator = SpecificationTranslator.forPrecondition(var(HEAP_VAR).toString(), parameters);
      BPLExpression pre = translator.translate(context, requires);
      return implies(pre, expr);
    }
    return BPLBoolLiteral.TRUE;
    // REVIEW[om]: Remove!
    // BMLStoreRef[] storeRefs =
    // project.getSpecificationDesugarer().getModifiesStoreRefs(method);
    // if (storeRefs.length > 0) {
    // String l = quantVarName("l");
    // ModifiesFilter filter =
    // ModifiesFilter.forMethod(oldHeap, parameters, l);
    // BPLExpression expr = filter.translate(context, storeRefs);
    // expr = logicalAnd(alive(rval(obj(var(l))), var(oldHeap)), expr);
    // BPLExpression left = get(var(HEAP_VAR), var(l));
    // BPLExpression right = get(var(oldHeap), var(l));
    // expr = implies(expr, isEqual(left, right));
    // BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
    // expr = forall(lVar, expr);
    // return expr;
    // }
    // return BPLBoolLiteral.TRUE;
  }

  private BPLExpression translateLoopFrame(
      BMLLoopModifiesClause modifies,
      InstructionHandle loopHead) {
    BMLStoreRef[] storeRefs = modifies.getStoreRefs();
    if (storeRefs.length > 0) {
      BasicBlock loopHeader = method.getCFG().findBlockStartingAt(loopHead);
      String loopHeap = getLoopHeapVar(loopHeader);
      String l = quantVarName("l");
      ModifiesFilter filter = ModifiesFilter.forLoop(
          loopHeap,
          PRE_HEAP_VAR,
          thisVar(),
          getLocalVariablesAt(loopHead),
          getStackVariablesAt(loopHead),
          getInParameters(),
          l);
      BPLExpression expr = filter.translate(context, storeRefs);
      expr = logicalAnd(alive(rval(obj(var(l))), var(loopHeap)), expr);
      BPLExpression left = get(var(HEAP_VAR), var(l));
      BPLExpression right = get(var(loopHeap), var(l));
      expr = implies(expr, isEqual(left, right));
      BPLVariable lVar = new BPLVariable(l, new BPLTypeName(LOCATION_TYPE));
      expr = forall(lVar, expr);
      return expr;
    }
    return BPLBoolLiteral.TRUE;
  }

  /**
   * Convenience method for translating an integer constant.
   * 
   * @param literal The integer constant to translate.
   * @return A BoogiePL expression representing the given integer constant.
   */
  private BPLExpression intLiteral(long literal) {
    return context.translateIntLiteral(literal);
  }

  /**
   * Convenience method for translating a type reference.
   * 
   * @param type The type reference to translate.
   * @return A BoogiePL expression representing the given type reference.
   */
  private BPLExpression typeRef(JType type) {
    return context.translateTypeReference(type);
  }

  /**
   * Starts a new BoogiePL block with the given {@code label} in the current
   * translation. BoogiePL commands generated during the translation are then
   * added to this new block until it is closed.
   * 
   * @param label The label of the new BoogiePL block.
   */
  private void startBlock(String label) {
    blockLabel = label;
    commands = new ArrayList<BPLCommand>();
  }

  /**
   * Returns whether a BoogiePL block is currently active meaning that it has
   * been opened but not closed yet.
   * 
   * @return Whether a BoogiePL block is currently active in the translation.
   */
  private boolean isInsideBlock() {
    return blockLabel != null;
  }

  /**
   * Adds the given {@code command} to the currently active BoogiePL block.
   * 
   * @param command The command to add to the currently active BoogiePL block.
   */
  private void addCommand(BPLCommand command) {
    commands.add(command);
  }

  /**
   * Adds an assignment for the given operands to the currently active BoogiePL
   * block.
   * 
   * @param lhs The LHS expression of the assignment.
   * @param rhs The RHS expression of the assignment.
   */
  private void addAssignment(BPLExpression lhs, BPLExpression rhs) {
    addCommand(new BPLAssignmentCommand(lhs, rhs));
  }

  /**
   * Adds an assertion for the given {@code expression} to the currently active
   * BoogiePL block.
   * 
   * @param expression The assertion's expression.
   */
  private void addAssert(BPLExpression expression) {
    addCommand(new BPLAssertCommand(expression));
  }

  /**
   * Adds an assumption for the given {@code expression} to the currently active
   * BoogiePL block.
   * 
   * @param expression The assumption's expression.
   */
  private void addAssume(BPLExpression expression) {
    addCommand(new BPLAssumeCommand(expression));
  }

  /**
   * Adds a havoc statement for the given {@code variables} to the currently
   * active BoogiePL block.
   * 
   * @param variables The variables of the havoc statement.
   */
  private void addHavoc(BPLVariableExpression... variables) {
    addCommand(new BPLHavocCommand(variables));
  }

  /**
   * Ends the currently active BoogiePL block and terminates it by the given
   * {@code transferCommand}.
   * 
   * @param transferCommand The transfer command of the BoogiePL block to
   *          terminate.
   */
  private void endBlock(BPLTransferCommand transferCommand) {
    BPLBasicBlock block = new BPLBasicBlock(
        blockLabel,
        commands.toArray(new BPLCommand[commands.size()]),
        transferCommand
    );
    blocks.add(block);
    blockLabel = null;
  }

  /**
   * Ends the currently active BoogiePL block and terminates it by a transfer
   * command which branches to the blocks identified by the given, and possibly
   * empty, set of {@code labels}.
   * 
   * @param labels The labels identifying the BoogiePL blocks to which the block
   *          being closed should branch.
   */
  private void endBlock(String... labels) {
    if (labels.length == 0) {
      endBlock(new BPLReturnCommand());
    } else {
      endBlock(new BPLGotoCommand(labels));
    }
  }

  /**
   * Ends the currently active BoogiePL block by a transfer command which
   * branches to the BoogiePL block representing the target of the given
   * {@code cfgEdge} of the method's control flow graph. This method should be
   * used whenever the reason for terminating a BoogiePL block is an explicit
   * edge in the method's control flow graph. Beside the actual termination of
   * the current BoogiePL block, this method treats back edges and other
   * branches to loop headers specially by asserting the decreasing nature of
   * loop variant expressions (only along back edges) and by keeping a copy of
   * the current heap (only along non-back-edges to loop headers).
   * 
   * @param cfgEdge The edge in the method's control flow graph which triggers
   *          the termination of the current BoogiePL block.
   */
  private void endBlock(Edge cfgEdge) {
    BasicBlock cfgBlock = cfgEdge.getTarget();
    if (cfgBlock.isBackEdgeTarget()) {
      InstructionHandle insn = cfgBlock.getFirstInstruction();
      for (BMLLoopSpecification loopSpec : getLoopSpecificationsAt(cfgBlock)) {
        if (cfgEdge.isBackEdge()) {
          BMLLoopVariant variant = loopSpec.getVariant();
          // REVIEW[om]: This is a temporary hack to cope with what JACK gives
          // us.
          if (!(variant.getExpression() instanceof BMLIntLiteral)) {
            // Assert that the loop variant expression indeed decreased in the
            // current iteration. To that end, we use the old value of that
            // expression as previously evaluated and stored at the
            // corresponding loop header.
            String variantVar = getLoopVariantVar(variant);
            addAssert(less(translateLoopVariant(variant, insn), var(variantVar)));
          }
        } else {
          // If we are branching to a loop header along a non-back-edge, we
          // keep a copy of the current heap which is used at the loop header
          // itself for translating loop invariants.
          String loopHeap = getLoopHeapVar(cfgEdge.getTarget());
          addAssignment(var(loopHeap), var(HEAP_VAR));
        }
      }
    }

    // Now, do the actual branch.
    endBlock(blockLabel(cfgEdge.getTarget()));
  }

  /**
   * Returns the name of the variable to use for storing a copy of the heap when
   * entering the loop starting at the given basic block of the method's control
   * flow graph.
   * 
   * @param cfgBlock The basic block where the loop starts.
   * @return The name of the loop heap variable.
   */
  private String getLoopHeapVar(BasicBlock cfgBlock) {
    String var = loopHeapVars.get(cfgBlock);
    if (var == null) {
      var = LOOP_HEAP_VAR_PREFIX + loopHeapVars.size();
      loopHeapVars.put(cfgBlock, var);
    }
    return var;
  }

  /**
   * Returns the name of the variable to use for storing a copy of the given
   * loop variant expression at the beginning of a loop.
   * 
   * @param variant The loop variant in question.
   * @return The name of the variable to store the value of the loop variant
   *         expression.
   */
  private String getLoopVariantVar(BMLLoopVariant variant) {
    String var = loopVariantVars.get(variant);
    if (var == null) {
      var = LOOP_VARIANT_VAR_PREFIX + loopVariantVars.size();
      loopVariantVars.put(variant, var);
    }
    return var;
  }

  /**
   * Returns the label to be used for a BoogiePL block representing the given
   * basic block of the method's control flow graph. The label is guaranteed to
   * be unique.
   * 
   * @param cfgBlock The basic block of the control flow graph.
   * @return The label for the BoogiePL block.
   */
  private static String blockLabel(BasicBlock cfgBlock) {
    String label = BLOCK_LABEL_PREFIX + cfgBlock.getID();
    if (cfgBlock.isBackEdgeTarget()) {
      label += LOOP_BLOCK_LABEL_SUFFIX;
    }
    return label;
  }

  /**
   * Returns the label to be used for a BoogiePL block where the exceptional
   * postcondition of the given {@code exception} is checked at the end of a
   * method. The label is guaranteed to be unique.
   * 
   * @param exception The exception by which the method terminated.
   * @return The label to be used for the exceptional exit block.
   */
  private static String postXBlockLabel(JType exception) {
    return POSTX_BLOCK_LABEL_PREFIX + exception.getName();
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for assuming that the guard of a conditional branch has evaluated
   * to {@code true}. The label is guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the conditional branch appears.
   * @return The label to be used for the BoogiePL block.
   */
  private String trueBranchBlockLabel(BasicBlock cfgBlock) {
    return blockLabel(cfgBlock) + TRUE_BLOCK_LABEL_SUFFIX;
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for assuming that the guard of a conditional branch has evaluated
   * to {@code false}. The label is guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the conditional branch appears.
   * @return The label to be used for the BoogiePL block.
   */
  private String falseBranchBlockLabel(BasicBlock cfgBlock) {
    return blockLabel(cfgBlock) + FALSE_BLOCK_LABEL_SUFFIX;
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for a concrete case statement of a switch statement and which
   * assumes that the constant of the switch statement has the given {@code key}
   * as its value. The label is guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the switch statement appears.
   * @param key The key of the concrete case statement.
   * @return The label to be used for the BoogiePL block.
   */
  private String caseBlockLabel(BasicBlock cfgBlock, int key) {
    return blockLabel(cfgBlock) + CASE_BLOCK_LABEL_SUFFIX + key;
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for the default statement of a switch statement and which assumes
   * that the constant of the switch statement has a value different from all
   * the values handled by the individual case statements. The label is
   * guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the switch statement appears.
   * @return The label to be used for the BoogiePL block.
   */
  private String defaultBlockLabel(BasicBlock cfgBlock) {
    return blockLabel(cfgBlock) + DEFAULT_BLOCK_LABEL_SUFFIX;
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for method calls having declared checked exceptions in case the
   * method terminates without throwing any exception. The label is guaranteed
   * to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the method call appears.
   * @return The label to be used for the BoogiePL block.
   */
  private String normalPostBlockLabel(BasicBlock cfgBlock) {
    return blockLabel(cfgBlock) + NO_EXCEPTION_BLOCK_LABEL_SUFFIX;
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for method calls having declared checked exceptions in case the
   * method terminates by throwing the given {@code exception}. The label is
   * guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the method call appears.
   * @param exception The exception thrown by the method.
   * @return The label to be used for the BoogiePL block.
   */
  private String exceptionalPostBlockLabel(BasicBlock cfgBlock, JType exception) {
    return blockLabel(cfgBlock) + EXCEPTION_BLOCK_LABEL_SUFFIX
        + exception.getName();
  }

  /**
   * Returns the label to be used for the synthetic BoogiePL block which is
   * generated for branches to exception handlers when some exception is thrown.
   * The label is guaranteed to be unique.
   * 
   * @param cfgBlock The basic block of the method's control flow graph in which
   *          the branch to the exception handler appears.
   * @param exception The exception caught by the exception handler.
   * @return The label to be used for the BoogiePL block.
   */
  private String handlerBlockLabel(BasicBlock cfgBlock, JType exception) {
    return blockLabel(cfgBlock) + HANDLER_BLOCK_LABEL_SUFFIX
        + exception.getName();
  }

  private static String typeAbbrev(BPLType type) {
    return (type == BPLBuiltInType.INT) ? INT_TYPE_ABBREV : REF_TYPE_ABBREV;
  }

  private static String paramVar(int index) {
    return PARAM_VAR_PREFIX + index;
  }

  private static String thisVar() {
    return paramVar(0);
    // return THIS_VAR;
  }

  private static String localVar(int index, JType type) {
    return LOCAL_VAR_PREFIX + index + typeAbbrev(type(type));
  }

  private static String intLocalVar(int index) {
    return LOCAL_VAR_PREFIX + index + INT_TYPE_ABBREV;
  }

  private static String refLocalVar(int index) {
    return LOCAL_VAR_PREFIX + index + REF_TYPE_ABBREV;
  }

  private static String stackVar(int index, JType type) {
    return STACK_VAR_PREFIX + index + typeAbbrev(type(type));
  }

  private static String intStackVar(int index) {
    return STACK_VAR_PREFIX + index + INT_TYPE_ABBREV;
  }

  private static String refStackVar(int index) {
    return STACK_VAR_PREFIX + index + REF_TYPE_ABBREV;
  }

  private static String returnStateVar(int index) {
    return RETURN_STATE_VAR + index;
  }

  private static String returnValueVar(int index, JType type) {
    return RETURN_VALUE_VAR + index + typeAbbrev(type(type));
  }

  private static String intReturnValueVar(int index) {
    return RETURN_VALUE_VAR + index + INT_TYPE_ABBREV;
  }

  private static String refReturnValueVar(int index) {
    return RETURN_VALUE_VAR + index + REF_TYPE_ABBREV;
  }

  private static String exceptionVar(int index) {
    return EXCEPTION_VAR + index;
  }

  private static String swapVar(JType type) {
    return SWAP_VAR_PREFIX + typeAbbrev(type(type));
  }

  /**
   * The visitor performing the actual translation of the bytecode instructions.
   * 
   * @author Ovidio Mallo
   */
  private final class InstructionTranslator implements IInstructionVisitor {

    /**
     * The basic block in the method's control flow graph to which the
     * instruction being translated belongs. Should be updated by the
     * {@code MethodTranslator} as appropriate.
     */
    private BasicBlock cfgBlock;

    /**
     * The instruction handle of the instruction being translated. Should be
     * updated by the {@code MethodTranslator} as appropriate.
     */
    private InstructionHandle handle;

    /**
     * Translates the occurrence of a runtime exception as thrown by the
     * bytecode instruction currently being translated.
     * 
     * @param exceptionName The name of the runtime exception eventually thrown.
     * @param normalConditions The conditions under which the runtime exception
     *          does <i>not</i> occur.
     */
    private void translateRuntimeException(
        String exceptionName,
        BPLExpression... normalConditions) {
      // If we are not modeling runtime exceptions, we simply rule them out
      // by asserting that the conditions under which the runtime exception
      // occurs do not hold.
      if (!project.isModelRuntimeExceptions()) {
        for (BPLExpression normalCondition : normalConditions) {
          addAssert(normalCondition);
        }
        return;
      }

      // Let's find the exception handler basic block which will catch the
      // runtime exception. Note that we will always have at most one exception
      // handler since for runtime exceptions we know the exact runtime type
      // of the exception being thrown meaning that we will never branch to
      // an exception handler whose handler type is a proper subtype of the
      // runtime exception (as is usually necessary for other exceptions thrown
      // e.g. by method calls or the ATHROW instruction).
      JType exception = TypeLoader.getClassType(exceptionName);
      Set<String> labels = new LinkedHashSet<String>();
      for (ExceptionHandler handler : method.getExceptionHandlers()) {
        if (handler.isActiveFor(handle)) {
          if (exception.isSubtypeOf(handler.getType())) {
            InstructionHandle target = handler.getHandler();
            labels.add(blockLabel(method.getCFG().findBlockStartingAt(target)));
            break;
          }
        }
      }
      // If we have not found any exception handler for the runtime exception,
      // we search for a matching checked exception of the method.
      if (labels.size() == 0) {
        for (JClassType methodException : method.getExceptionTypes()) {
          if (exception.isSubtypeOf(methodException)) {
            labels.add(postXBlockLabel(methodException));
          }
        }
        // In any case, we have to at least branch to the exit block which
        // contains the proof obligations which must be satisfied even if the
        // method terminates with an exception.
        if (labels.size() == 0) {
          labels.add(EXIT_BLOCK_LABEL);
        }
      }

      // Construct the names of the synthetic BoogiePL blocks which will assume
      // the conditions under which a runtime exception is thrown or not,
      // respectively.
      String trueBlock = blockLabel(cfgBlock)
          + RUNTIME_EXCEPTION_TRUE_BLOCK_LABEL_SUFFIX + exception.getName();
      String falseBlock = blockLabel(cfgBlock)
          + RUNTIME_EXCEPTION_FALSE_BLOCK_LABEL_SUFFIX + exception.getName();
      endBlock(trueBlock, falseBlock);

      // First, we generate the block which handles the thrown exception.
      startBlock(trueBlock);
      addAssume(logicalNot(logicalAnd(normalConditions)));
      // Havoc the exception object and assume its static type.
      // addHavoc(var(refStackVar(0)));
      // addAssume(alive(rval(var(refStackVar(0))), var(HEAP_VAR)));
      // addAssume(nonNull(var(refStackVar(0))));
      addAssume(isEqual(typ(rval(var(refStackVar(0)))), typeRef(exception)));
      endBlock(labels.toArray(new String[labels.size()]));

      // Subsequently, we generate the block for the case where no exception is
      // thrown. Note that we do not end this BoogiePL block since the
      // translation of the instruction throwing the runtime exception can be
      // directly appended to it.
      startBlock(falseBlock);
      addAssume(logicalAnd(normalConditions));
    }

    public void visitNopInstruction(NopInstruction insn) {
      // do nothing
    }

    public void visitILoadInstruction(ILoadInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      int local = insn.getIndex();
      addAssignment(var(intStackVar(stack)), var(intLocalVar(local)));
    }

    public void visitLLoadInstruction(LLoadInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      int local = insn.getIndex();
      addAssignment(var(intStackVar(stack)), var(intLocalVar(local)));
    }

    public void visitALoadInstruction(ALoadInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      int local = insn.getIndex();
      addAssignment(var(refStackVar(stack)), var(refLocalVar(local)));
    }

    public void visitIStoreInstruction(IStoreInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      int local = insn.getIndex();
      addAssignment(var(intLocalVar(local)), var(intStackVar(stack)));
    }

    public void visitLStoreInstruction(LStoreInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      int local = insn.getIndex();
      addAssignment(var(intLocalVar(local)), var(intStackVar(stack)));
    }

    public void visitAStoreInstruction(AStoreInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      int local = insn.getIndex();
      addAssignment(var(refLocalVar(local)), var(refStackVar(stack)));
    }

    public void visitVConstantInstruction(VConstantInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      int constant = insn.getConstant();
      addAssignment(var(intStackVar(stack)), intLiteral(constant));
    }

    public void visitLdcInstruction(LdcInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      Object constant = insn.getConstant();
      if (constant instanceof Integer) {
        Integer integer = (Integer) constant;
        addAssignment(var(intStackVar(stack)), intLiteral(integer.intValue()));
      } else if (constant instanceof Long) {
        Long integer = (Long) constant;
        addAssignment(var(intStackVar(stack)), intLiteral(integer.intValue()));
      } else if (constant instanceof String) {
        String string = (String) constant;
        BPLExpression stringExpr = context.translateStringLiteral(string);
        addAssignment(var(refStackVar(stack)), stringExpr);
      } else if (constant instanceof JType) {
        JType type = (JType) constant;
        BPLExpression typeExpr = context.translateClassLiteral(type);
        addAssignment(var(refStackVar(stack)), typeExpr);
      }
    }

    public void visitAConstNullInstruction(AConstNullInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      addAssignment(var(refStackVar(stack)), nullLiteral());
    }

    public void visitGetFieldInstruction(GetFieldInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      BCField field = insn.getField();

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(refStackVar(stack))));

      BPLExpression ref = var(refStackVar(stack));
      BPLExpression get = fieldAccess(context, HEAP_VAR, ref, field);
      addAssignment(var(stackVar(stack, field.getType())), get);
    }

    public void visitPutFieldInstruction(PutFieldInstruction insn) {
      int stackLhs = handle.getFrame().getStackSize() - 2;
      int stackRhs = handle.getFrame().getStackSize() - 1;
      BCField field = insn.getField();

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(refStackVar(stackLhs))));

      BPLExpression lhs = var(refStackVar(stackLhs));
      BPLExpression rhs = var(stackVar(stackRhs, field.getType()));
      BPLExpression update = fieldUpdate(context, HEAP_VAR, lhs, field, rhs);
      addAssignment(var(HEAP_VAR), update);
    }

    public void visitGetStaticInstruction(GetStaticInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      BCField field = insn.getField();

      BPLExpression get = fieldAccess(context, HEAP_VAR, null, field);
      addAssignment(var(stackVar(stack, field.getType())), get);
    }

    public void visitPutStaticInstruction(PutStaticInstruction insn) {
      int stackRhs = handle.getFrame().getStackSize() - 1;
      BCField field = insn.getField();

      BPLExpression rhs = var(stackVar(stackRhs, field.getType()));
      BPLExpression update = fieldUpdate(context, HEAP_VAR, null, field, rhs);
      addAssignment(var(HEAP_VAR), update);
    }

    private void translateArrayLoadInstruction() {
      int stackRef = handle.getFrame().getStackSize() - 2;
      int stackIdx = handle.getFrame().getStackSize() - 1;
      JArrayType arrayType = (JArrayType) handle.getFrame().peek(stackRef);
      JType elemType = arrayType.getIndexedType();
      String ref = refStackVar(stackRef);
      String idx = intStackVar(stackIdx);

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(ref)));
      translateRuntimeException(
          "java.lang.ArrayIndexOutOfBoundsException",
          lessEqual(intLiteral(0), var(idx)),
          less(var(idx), arrayLength(rval(var(ref)))));

      BPLExpression get = arrayAccess(HEAP_VAR, arrayType, var(ref), var(idx));
      addAssignment(var(stackVar(stackRef, elemType)), get);
    }

    public void visitVALoadInstruction(VALoadInstruction insn) {
      translateArrayLoadInstruction();
    }

    public void visitAALoadInstruction(AALoadInstruction insn) {
      translateArrayLoadInstruction();
    }

    private void translateArrayStoreInstruction() {
      int stackRef = handle.getFrame().getStackSize() - 3;
      int stackIdx = handle.getFrame().getStackSize() - 2;
      int stackVal = handle.getFrame().getStackSize() - 1;
      JArrayType arrayType = (JArrayType) handle.getFrame().peek(stackRef);
      JType elemType = arrayType.getIndexedType();
      String ref = refStackVar(stackRef);
      String idx = intStackVar(stackIdx);
      String val = stackVar(stackVal, elemType);

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(ref)));
      translateRuntimeException(
          "java.lang.ArrayIndexOutOfBoundsException",
          lessEqual(intLiteral(0), var(idx)),
          less(var(idx), arrayLength(rval(var(ref)))));
      if (elemType.isReferenceType()) {
        translateRuntimeException("java.lang.ArrayStoreException", isOfType(
            rval(var(val)),
            elementType(typ(rval(var(ref))))));
      }

      BPLExpression update = arrayUpdate(
          HEAP_VAR,
          arrayType,
          var(ref),
          var(idx),
          var(val));
      addAssignment(var(HEAP_VAR), update);
    }

    public void visitVAStoreInstruction(VAStoreInstruction insn) {
      translateArrayStoreInstruction();
    }

    public void visitAAStoreInstruction(AAStoreInstruction insn) {
      translateArrayStoreInstruction();
    }

    public void visitArrayLengthInstruction(ArrayLengthInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      String ref = refStackVar(stack);

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(ref)));

      addAssignment(var(intStackVar(stack)), arrayLength(rval(var(ref))));
    }

    private boolean isSuperConstructorCall(
        BCMethod invokedMethod,
        InstructionHandle handle) {
      if (invokedMethod.isConstructor()) {
        JType[] params = invokedMethod.getRealParameterTypes();
        int receiver = handle.getFrame().getStackSize() - params.length;
        JType receiverType = handle.getFrame().peek(receiver);
        return !receiverType.equals(invokedMethod.getOwner());
      }
      return false;
    }

    /**
     * Method to translate the different kinds of method call instructions.
     * 
     * @param insn The method call instruction to translate.
     * @deprecated
     */
    /*
    private void translateInvokeInstructionOld(InvokeInstruction insn) {
      BCMethod invokedMethod = insn.getMethod();
      JType[] params = invokedMethod.getRealParameterTypes();
      int first = handle.getFrame().getStackSize() - params.length;

      // Non-static method calls may throw a NullPointerException.
      if (!invokedMethod.isStatic()) {
        translateRuntimeException(
            "java.lang.NullPointerException",
            nonNull(var(refStackVar(first))));
      }

      // Assert the invariants on the relevant objects.
      // If the this object has not been initialized yet (inside a constructor),
      // its invariant is not required to hold.
      assertExposedInvariants(!handle.isThisInitialized());

      // Start the actual desugaring of the method call.

      // Collect the names of the method's actual arguments and check that the
      // method's precondition holds.
      String[] args = new String[params.length];
      for (int i = 0; i < params.length; i++) {
        args[i] = stackVar(first + i, params[i]);
      }
      addAssert(translatePrecondition(invokedMethod, args));

      // Keep a copy of the heap in the method's pre-state and havoc the current
      // heap.
      //@deprecated addAssignment(var(PRE_HEAP_VAR), var(HEAP_VAR));
      addHavoc(var(HEAP_VAR));

      // Assume that no objects are de-allocated during the execution of the
      // method. Note that this assumption ignores the effect of any potential
      // garbage collector.
      String v = quantVarName("v");
      BPLVariable vVar = new BPLVariable(v, new BPLTypeName(VALUE_TYPE));
      addAssume(forall(vVar, implies(alive(var(v), var(PRE_HEAP_VAR)), alive(
          var(v),
          var(HEAP_VAR)))));

      // Assume the method's frame condition.
      addAssume(translateMethodFrame(invokedMethod, args));

      // Assume the object invariants as justified by the verification
      // methodology.
      if (isSuperConstructorCall(invokedMethod, handle)) {
        // Right after a super constructor call we may only assume the
        // supertype's invariants on the this object but not the invariants of
        // the current class, so we exclude the this object.
        assumeAllInvariants(true);

        // For the this object, only assume the invariants of its supertype.
        BPLExpression type = typeRef(invokedMethod.getOwner());
        addAssume(inv(type, var(thisVar()), var(HEAP_VAR)));
      } else {
        // Assume the invariants of all objects, including the this object.
        assumeAllInvariants(false);
      }

      JClassType[] exceptions = invokedMethod.getExceptionTypes();
      if (exceptions.length > 0) {
        // For every exception thrown by the method call, we create a synthetic
        // BoogiePL block in which we assume the corresponding exceptional
        // postcondition.

        // Branch to the blocks modeling the normal and the individual
        // exceptional terminations of the method call.
        String[] labels = new String[exceptions.length + 1];
        labels[0] = normalPostBlockLabel(cfgBlock);
        for (int i = 0; i < exceptions.length; i++) {
          labels[i + 1] = exceptionalPostBlockLabel(cfgBlock, exceptions[i]);
        }
        endBlock(labels);

        for (JClassType exception : exceptions) {
          // Create the actual blocks for the individual exceptions and assume
          // the corresponding exceptional postcondition.
          startBlock(exceptionalPostBlockLabel(cfgBlock, exception));

          // Havoc the exception object and assume its static type.
          addHavoc(var(refStackVar(0)));
          addAssume(alive(rval(var(refStackVar(0))), var(HEAP_VAR)));
          addAssume(isInstanceOf(rval(var(refStackVar(0))), typeRef(exception)));

          // Assume the corresponding exceptional postcondition.
          addAssume(translateXPostcondition(
              invokedMethod,
              exception,
              refStackVar(0),
              args));

          // Now, branch to the actual exception handlers.
          branchToHandlers(exception);
        }

        translateReachableExceptionHandlers();

        // Finally, open the BoogiePL block representing the normal termination
        // of the method. The subsequent translation can simply continue inside
        // this block.
        startBlock(normalPostBlockLabel(cfgBlock));
      }

      JType returnType = invokedMethod.getReturnType();
      String resultVar = "N/A"; // callResultVar(returnType);

      // If the method has a return value, we havoc it and assume its static
      // type.
      if (!invokedMethod.isVoid()) {
        addHavoc(var(resultVar));
        if (returnType.isReferenceType()) {
          addAssume(alive(rval(var(resultVar)), var(HEAP_VAR)));
          addAssume(isOfType(rval(var(resultVar)), typeRef(returnType)));
        } else {
          addAssume(isOfType(ival(var(resultVar)), typeRef(returnType)));
        }
      }

      // Assume the method's normal postcondition.
      addAssume(translatePostcondition(
          invokedMethod,
          resultVar,
          args));

      // If the method has a return value, we copy the helper variable
      // callResult to the actual stack variable which will hold the value.
      if (!invokedMethod.isVoid()) {
        String resultStackVar = stackVar(first, returnType);
        addAssignment(var(resultStackVar), var(resultVar));
      }
    }
    */
    
    /**
     * Method to translate the different kinds of method call instructions.
     * 
     * @param insn The method call instruction to translate.
     */
    private void translateInvokeInstruction(InvokeInstruction insn) {
      BCMethod invokedMethod = insn.getMethod();
      JType[] params = invokedMethod.getRealParameterTypes();
      int first = handle.getFrame().getStackSize() - params.length;
      
      boolean provideReturnValue = !invokedMethod.isVoid() || invokedMethod.isConstructor();
           
      JType retType = (invokedMethod.isConstructor()
        ? invokedMethod.getOwner()
        : invokedMethod.getReturnType()
      );

      // Non-static method calls may throw a NullPointerException.
      if (!invokedMethod.isStatic() && !invokedMethod.isConstructor()) {
        translateRuntimeException(
            "java.lang.NullPointerException",
            nonNull(var(refStackVar(first))));
      }

      /*
      if (!invokedMethod.isConstructor()) {
        // addAssume(alive(rval(var(refStackVar(0))), var(HEAP_VAR)));
        addAssume(alive(rval(var(stackVar(first, params[0]))), var(HEAP_VAR)));
      }
      */

      // Prepare return values of method call
      List<BPLVariableExpression> resultVars = new ArrayList<BPLVariableExpression>();
      //@deprecated resultVars.add(new BPLVariableExpression(HEAP_VAR));
      resultVars.add(new BPLVariableExpression(returnStateVar(callStatements)));

      /*
      boolean isConstructor = invokedMethod.isConstructor()
          || invokedMethod.getQualifiedName().contains(Constants.CONSTRUCTOR_NAME);
      */
      
      if (provideReturnValue) {
        resultVars.add(new BPLVariableExpression(returnValueVar(callStatements, retType)));
      }
      resultVars.add(new BPLVariableExpression(exceptionVar(callStatements)));

      // Prepare arguments of method call
      List<BPLExpression> methodParams = new ArrayList<BPLExpression>();
      
      // Pass heap variable as first method argument
      //@deprecated methodParams.add(new BPLVariableExpression(HEAP_VAR));
      
      // Pass all other method arguments (the first of which refers to the "this" object
      // if the method is not static.
      String[] args = new String[params.length];
      for (int i = 0; i < params.length; i++) {
        args[i] = stackVar(first + i, params[i]);
        methodParams.add(new BPLVariableExpression(args[i]));
      }

      // Create call command
      BPLCommand callCmd = new BPLCallCommand(
          getProcedureName(invokedMethod),
          methodParams.toArray(new BPLExpression[methodParams.size()]),
          resultVars.toArray(new BPLVariableExpression[resultVars.size()])
      );
      addCommand(callCmd);

      
      // TODO/FIXME If the current method call initialized this object
      // (i.e. we call Object..init() in A..init(), set this-variable correctly.
      if (method.isConstructor() &&
          invokedMethod.isConstructor() &&
          method.getReturnType() == invokedMethod.getReturnType()) {
        addAssignment(var(refLocalVar(0)), var(returnValueVar(callStatements, retType)));
      }
      
      if (provideReturnValue) {
        
        // TODO assign returned method result to the topmost stack variable
        /*
        addAssignment(
            var(stackVar(0, retType)),
            new BPLVariableExpression(returnValueVar(callStatements, retType))
        );
        */
      }

      // Assume exceptional postcondition for all exceptions
      // and jump to the appropriate exception handler defined below.

      JClassType[] exceptions = invokedMethod.getExceptionTypes();
      //if (exceptions.length > 0) {
        // For every exception thrown by the method call, we create a synthetic
        // BoogiePL block in which we assume the corresponding exceptional
        // postcondition.

        // Branch to the blocks modeling the normal and the individual
        // exceptional terminations of the method call.
        String[] labels = new String[exceptions.length + 1];
        labels[0] = normalPostBlockLabel(cfgBlock) + "_" + callStatements;
        for (int i = 0; i < exceptions.length; i++) {
          labels[i + 1] = exceptionalPostBlockLabel(cfgBlock, exceptions[i]) + "_" + callStatements;
        }
        endBlock(labels);

        for (JClassType exception : exceptions) {
          // Create the actual blocks for the individual exceptions.
          // It is not necessary to check the exceptional postcondition,
          // for this will be implicitely done by Boogie.
          startBlock(exceptionalPostBlockLabel(cfgBlock, exception) + "_" + callStatements);

          // Havoc the exception object and assume its static type.
          /*
          addHavoc(var(exceptionVar(callStatements)));
          addAssume(alive(
              rval(var(exceptionVar(callStatements))),
              var(HEAP_VAR)));
          addAssume(isInstanceOf(
              rval(var(exceptionVar(callStatements))),
              typeRef(exception)));
          addAssume(isExceptionalReturnState(var(RETURN_STATE_VAR + callStatements)));
          */
          
          addAssume(logicalAnd(
              isExceptionalReturnState(var(RETURN_STATE_VAR + callStatements)),
              isInstanceOf(
                  rval(var(exceptionVar(callStatements))),
                  typeRef(exception))
          ));

          // Assume the corresponding exceptional postcondition.
          /*
           * addAssume(translateXPostcondition( invokedMethod, exception,
           * PRE_HEAP_VAR, refStackVar(0), args));
           */

          // Now, branch to the actual exception handlers.
          branchToHandlers(exception);
        }

        translateReachableExceptionHandlers();

        // Finally, open the BoogiePL block representing the normal termination
        // of the method. The subsequent translation can simply continue inside
        // this block.
        startBlock(normalPostBlockLabel(cfgBlock) + "_" + callStatements);
      //}

      // JType returnType = invokedMethod.getReturnType();
      String resultVar = returnValueVar(callStatements, retType);

      // If the method has a return value, we havoc it and assume its static type.
      if (provideReturnValue) {
        addHavoc(var(resultVar));
        if (retType.isReferenceType()) {
          addAssume(alive(rval(var(resultVar)), var(HEAP_VAR)));
          addAssume(isOfType(rval(var(resultVar)), typeRef(retType)));
        } else {
          addAssume(isOfType(ival(var(resultVar)), typeRef(retType)));
        }
        /*deprecated 
        if (method.isConstructor()) {
          addAssume(isOfType(rval(var(RETURN_VALUE_PARAM)), typeRef(method.getOwner())));
        } else {
          addAssume(isOfType(rval(var(RETURN_VALUE_PARAM)), typeRef(method.getReturnType())));
        }
        */
      }
      addAssume(isNormalReturnState(var(RETURN_STATE_VAR + callStatements)));

      // It is not necessary to assume the method's normal postcondition.
      // This will be implicitely done by Boogie.
      /*
      addAssume(translatePostcondition(
          invokedMethod,
          resultVar,
          args));
      */

      // If the method has a return value, we copy the helper variable
      // callResult to the actual stack variable which will hold the value.
      if (provideReturnValue) {
        String resultStackVar = stackVar(first, retType);
        addAssignment(var(resultStackVar), var(resultVar));
      }

      callStatements++;
    }

    public void visitInvokeVirtualInstruction(InvokeVirtualInstruction insn) {
      translateInvokeInstruction(insn);
    }

    public void visitInvokeStaticInstruction(InvokeStaticInstruction insn) {
      translateInvokeInstruction(insn);
    }

    public void visitInvokeSpecialInstruction(InvokeSpecialInstruction insn) {
      translateInvokeInstruction(insn);
    }

    public void visitInvokeInterfaceInstruction(InvokeInterfaceInstruction insn) {
      translateInvokeInstruction(insn);
    }

    private void translateBinArithInstruction(int opcode) {
      int stackLeft = handle.getFrame().getStackSize() - 2;
      int stackRight = handle.getFrame().getStackSize() - 1;
      String left = intStackVar(stackLeft);
      String right = intStackVar(stackRight);
      BPLExpression expr;
      switch (opcode) {
        case IOpCodes.IADD:
        case IOpCodes.LADD:
          expr = add(var(left), var(right));
          break;
        case IOpCodes.ISUB:
        case IOpCodes.LSUB:
          expr = sub(var(left), var(right));
          break;
        case IOpCodes.IMUL:
        case IOpCodes.LMUL:
          expr = multiply(var(left), var(right));
          break;
        case IOpCodes.IDIV:
        case IOpCodes.LDIV:
          translateRuntimeException("java.lang.ArithmeticException", notEqual(
              var(right),
              intLiteral(0)));
          expr = divide(var(left), var(right));
          break;
        case IOpCodes.IREM:
        case IOpCodes.LREM:
        default:
          translateRuntimeException("java.lang.ArithmeticException", notEqual(
              var(right),
              intLiteral(0)));
          expr = modulo(var(left), var(right));
          break;
      }
      addAssignment(var(intStackVar(stackLeft)), expr);
    }

    public void visitIBinArithInstruction(IBinArithInstruction insn) {
      translateBinArithInstruction(insn.getOpcode());
    }

    public void visitLBinArithInstruction(LBinArithInstruction insn) {
      translateBinArithInstruction(insn.getOpcode());
    }

    private void translateBitwiseInstruction(int opcode) {
      int stackLeft = handle.getFrame().getStackSize() - 2;
      int stackRight = handle.getFrame().getStackSize() - 1;
      String left = intStackVar(stackLeft);
      String right = intStackVar(stackRight);
      BPLExpression expr;
      switch (opcode) {
        case IOpCodes.ISHL:
        case IOpCodes.LSHL:
          expr = bitShl(var(left), var(right));
          break;
        case IOpCodes.ISHR:
        case IOpCodes.LSHR:
          expr = bitShr(var(left), var(right));
          break;
        case IOpCodes.IUSHR:
        case IOpCodes.LUSHR:
          expr = bitUShr(var(left), var(right));
          break;
        case IOpCodes.IAND:
        case IOpCodes.LAND:
          expr = bitAnd(var(left), var(right));
          break;
        case IOpCodes.IOR:
        case IOpCodes.LOR:
          expr = bitOr(var(left), var(right));
          break;
        case IOpCodes.IXOR:
        case IOpCodes.LXOR:
        default:
          expr = bitXor(var(left), var(right));
          break;
      }
      addAssignment(var(intStackVar(stackLeft)), expr);
    }

    public void visitIBitwiseInstruction(IBitwiseInstruction insn) {
      translateBitwiseInstruction(insn.getOpcode());
    }

    public void visitLBitwiseInstruction(LBitwiseInstruction insn) {
      translateBitwiseInstruction(insn.getOpcode());
    }

    public void visitINegInstruction(INegInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      addAssignment(var(intStackVar(stack)), neg(var(intStackVar(stack))));
    }

    public void visitLNegInstruction(LNegInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      addAssignment(var(intStackVar(stack)), neg(var(intStackVar(stack))));
    }

    public void visitIIncInstruction(IIncInstruction insn) {
      int local = insn.getIndex();
      int constant = insn.getConstant();
      BPLExpression iinc = add(var(intLocalVar(local)), intLiteral(constant));
      addAssignment(var(intLocalVar(local)), iinc);
    }

    /**
     * Translates the given if instruction by modeling the program flow for the
     * cases in which the guard of the if instruction evaluates to {@code true}
     * or {@code false}.
     * 
     * @param insn The if instruction to translate.
     * @param cmpTrue The condition representing the guard of the if
     *          instruction.
     * @param cmpFalse The condition representing the negation of the guard of
     *          the if instruction.
     */
    private void translateIfInstruction(
        AbstractIfInstruction insn,
        BPLExpression cmpTrue,
        BPLExpression cmpFalse) {
      InstructionHandle target = insn.getTarget();
      BasicBlock targetBlock = method.getCFG().findBlockStartingAt(target);

      // Construct the names of the BoogiePL blocks modeling the cases in which
      // the instruction's guard evaluates to true or false, respectively.
      String trueBlock = trueBranchBlockLabel(cfgBlock);
      String falseBlock = falseBranchBlockLabel(cfgBlock);
      endBlock(trueBlock, falseBlock);

      // First, we generate the block modeling the case in which the guard of
      // the if instruction evaluates to true.
      startBlock(trueBlock);
      addAssume(cmpTrue);
      endBlock(cfgBlock.getSuccessorEdge(targetBlock));

      // Subsequently, we generate the block modeling the case in which the
      // guard of the if instruction evaluates to false. Note that we do not end
      // this BoogiePL block since the translation of subsequent bytecode
      // instructions can be appended to it as the case in which the guard
      // evaluates to false always represents a fall through edge.
      startBlock(falseBlock);
      addAssume(cmpFalse);
    }

    public void visitIfICmpInstruction(IfICmpInstruction insn) {
      String left = intStackVar(handle.getFrame().getStackSize() - 2);
      String right = intStackVar(handle.getFrame().getStackSize() - 1);
      BPLExpression cmpTrue;
      BPLExpression cmpFalse;
      switch (insn.getOpcode()) {
        case IOpCodes.IF_ICMPEQ:
          cmpTrue = isEqual(var(left), var(right));
          cmpFalse = notEqual(var(left), var(right));
          break;
        case IOpCodes.IF_ICMPNE:
          cmpTrue = notEqual(var(left), var(right));
          cmpFalse = isEqual(var(left), var(right));
          break;
        case IOpCodes.IF_ICMPLT:
          cmpTrue = less(var(left), var(right));
          cmpFalse = greaterEqual(var(left), var(right));
          break;
        case IOpCodes.IF_ICMPGE:
          cmpTrue = greaterEqual(var(left), var(right));
          cmpFalse = less(var(left), var(right));
          break;
        case IOpCodes.IF_ICMPGT:
          cmpTrue = greater(var(left), var(right));
          cmpFalse = lessEqual(var(left), var(right));
          break;
        case IOpCodes.IF_ICMPLE:
        default:
          cmpTrue = lessEqual(var(left), var(right));
          cmpFalse = greater(var(left), var(right));
          break;
      }
      translateIfInstruction(insn, cmpTrue, cmpFalse);
    }

    public void visitIfACmpInstruction(IfACmpInstruction insn) {
      String left = refStackVar(handle.getFrame().getStackSize() - 2);
      String right = refStackVar(handle.getFrame().getStackSize() - 1);
      BPLExpression cmpTrue;
      BPLExpression cmpFalse;
      switch (insn.getOpcode()) {
        case IOpCodes.IF_ACMPEQ:
          cmpTrue = isEqual(var(left), var(right));
          cmpFalse = notEqual(var(left), var(right));
          break;
        case IOpCodes.IF_ACMPNE:
        default:
          cmpTrue = notEqual(var(left), var(right));
          cmpFalse = isEqual(var(left), var(right));
          break;
      }
      translateIfInstruction(insn, cmpTrue, cmpFalse);
    }

    public void visitIfInstruction(IfInstruction insn) {
      String operand = intStackVar(handle.getFrame().getStackSize() - 1);
      BPLExpression cmpTrue;
      BPLExpression cmpFalse;
      switch (insn.getOpcode()) {
        case IOpCodes.IFEQ:
          cmpTrue = isEqual(var(operand), intLiteral(0));
          cmpFalse = notEqual(var(operand), intLiteral(0));
          break;
        case IOpCodes.IFNE:
          cmpTrue = notEqual(var(operand), intLiteral(0));
          cmpFalse = isEqual(var(operand), intLiteral(0));
          break;
        case IOpCodes.IFLT:
          cmpTrue = less(var(operand), intLiteral(0));
          cmpFalse = greaterEqual(var(operand), intLiteral(0));
          break;
        case IOpCodes.IFGE:
          cmpTrue = greaterEqual(var(operand), intLiteral(0));
          cmpFalse = less(var(operand), intLiteral(0));
          break;
        case IOpCodes.IFGT:
          cmpTrue = greater(var(operand), intLiteral(0));
          cmpFalse = lessEqual(var(operand), intLiteral(0));
          break;
        case IOpCodes.IFLE:
        default:
          cmpTrue = lessEqual(var(operand), intLiteral(0));
          cmpFalse = greater(var(operand), intLiteral(0));
          break;
      }
      translateIfInstruction(insn, cmpTrue, cmpFalse);
    }

    public void visitIfNonNullInstruction(IfNonNullInstruction insn) {
      String operand = refStackVar(handle.getFrame().getStackSize() - 1);
      translateIfInstruction(insn, nonNull(var(operand)), isNull(var(operand)));
    }

    public void visitIfNullInstruction(IfNullInstruction insn) {
      String operand = refStackVar(handle.getFrame().getStackSize() - 1);
      translateIfInstruction(insn, isNull(var(operand)), nonNull(var(operand)));
    }

    public void visitLCmpInstruction(LCmpInstruction insn) {
      String left = intStackVar(handle.getFrame().getStackSize() - 2);
      String right = intStackVar(handle.getFrame().getStackSize() - 1);

      BPLExpression expr = ifThenElse(
          greater(var(left), var(right)),
          intLiteral(1),
          ifThenElse(
              isEqual(var(left), var(right)),
              intLiteral(0),
              intLiteral(-1)));

      addAssignment(var(left), cast(expr, BPLBuiltInType.INT));
    }

    public void visitGotoInstruction(GotoInstruction insn) {
      InstructionHandle target = insn.getTarget();
      BasicBlock targetBlock = method.getCFG().findBlockStartingAt(target);
      endBlock(cfgBlock.getSuccessorEdge(targetBlock));
    }

    public void visitLookupSwitchInstruction(LookupSwitchInstruction insn) {
      String stackVar = intStackVar(handle.getFrame().getStackSize() - 1);

      int[] keys = insn.getKeys();
      List<String> labels = new ArrayList<String>();
      for (int i = 0; i < keys.length; i++) {
        labels.add(caseBlockLabel(cfgBlock, i));
      }
      labels.add(defaultBlockLabel(cfgBlock));
      endBlock(labels.toArray(new String[labels.size()]));

      InstructionHandle[] targets = insn.getTargets();
      for (int i = 0; i < targets.length; i++) {
        startBlock(caseBlockLabel(cfgBlock, i));
        addAssume(isEqual(var(stackVar), intLiteral(keys[i])));
        BasicBlock caseBlock = method.getCFG().findBlockStartingAt(targets[i]);
        endBlock(cfgBlock.getSuccessorEdge(caseBlock));
      }
      InstructionHandle dfltTarget = insn.getDefaultTarget();
      startBlock(defaultBlockLabel(cfgBlock));
      if (keys.length > 0) {
        BPLExpression expr = notEqual(var(stackVar), intLiteral(keys[0]));
        for (int i = 1; i < keys.length; i++) {
          expr = logicalAnd(expr, notEqual(var(stackVar), intLiteral(keys[i])));
        }
        addAssume(expr);
      }
      BasicBlock dfltBlock = method.getCFG().findBlockStartingAt(dfltTarget);
      endBlock(cfgBlock.getSuccessorEdge(dfltBlock));
    }

    public void visitTableSwitchInstruction(TableSwitchInstruction insn) {
      String stackVar = intStackVar(handle.getFrame().getStackSize() - 1);

      int minIdx = insn.getMinIndex();
      int maxIdx = insn.getMaxIndex();
      List<String> labels = new ArrayList<String>();
      for (int idx = minIdx; idx <= maxIdx; idx++) {
        labels.add(caseBlockLabel(cfgBlock, idx - minIdx));
      }
      labels.add(defaultBlockLabel(cfgBlock));
      endBlock(labels.toArray(new String[labels.size()]));

      InstructionHandle[] targets = insn.getTargets();
      for (int i = 0; i < targets.length; i++) {
        startBlock(caseBlockLabel(cfgBlock, i));
        addAssume(isEqual(var(stackVar), intLiteral(minIdx + i)));
        BasicBlock caseBlock = method.getCFG().findBlockStartingAt(targets[i]);
        endBlock(cfgBlock.getSuccessorEdge(caseBlock));
      }
      InstructionHandle dfltTarget = insn.getDefaultTarget();
      startBlock(defaultBlockLabel(cfgBlock));
      addAssume(logicalOr(less(var(stackVar), intLiteral(minIdx)), greater(
          var(stackVar),
          intLiteral(maxIdx))));
      BasicBlock dfltBlock = method.getCFG().findBlockStartingAt(dfltTarget);
      endBlock(cfgBlock.getSuccessorEdge(dfltBlock));
    }

    public void visitReturnInstruction(ReturnInstruction insn) {
      // endBlock(POST_BLOCK_LABEL);
      endBlock(EXIT_BLOCK_LABEL);
    }

    public void visitIReturnInstruction(IReturnInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;

      // addAssignment(var(RESULT_VAR), var(intStackVar(stack)));
      // endBlock(POST_BLOCK_LABEL);

      addAssignment(var(RETURN_STATE_PARAM), var(NORMAL_RETURN_STATE));
      addAssignment(var(RESULT_PARAM), var(intStackVar(stack)));
      endBlock(EXIT_BLOCK_LABEL);
    }

    public void visitLReturnInstruction(LReturnInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;

      // addAssignment(var(RESULT_VAR), var(intStackVar(stack)));
      // endBlock(POST_BLOCK_LABEL);

      addAssignment(var(RESULT_PARAM), var(intStackVar(stack)));
      endBlock(EXIT_BLOCK_LABEL);
    }

    public void visitAReturnInstruction(AReturnInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;

      // addAssignment(var(RESULT_VAR), var(refStackVar(stack)));
      // endBlock(POST_BLOCK_LABEL);

      addAssignment(var(RESULT_PARAM), var(refStackVar(stack)));
      endBlock(EXIT_BLOCK_LABEL);
    }

    public void visitAThrowInstruction(AThrowInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;

      translateRuntimeException(
          "java.lang.NullPointerException",
          nonNull(var(refStackVar(stack))));

      if (stack != 0) {
        addAssignment(var(refStackVar(0)), var(refStackVar(stack)));
      }

      branchToHandlers(handle.getFrame().peek());
      translateReachableExceptionHandlers();
    }

    public void visitNewInstruction(NewInstruction insn) {
      int stack = handle.getFrame().getStackSize();
      addHavoc(var(refStackVar(stack)));
      addAssume(isEqual(
          heapNew(context, var(HEAP_VAR), insn.getType()),
          rval(var(refStackVar(stack)))));
      addAssignment(var(HEAP_VAR), heapAdd(context, var(HEAP_VAR), insn
          .getType()));
    }

    private void translateNewArrayInstruction(JType allocationType) {
      int stack = handle.getFrame().getStackSize() - 1;
      String ref = refStackVar(stack);
      String len = intStackVar(stack);

      translateRuntimeException(
          "java.lang.NegativeArraySizeException",
          lessEqual(intLiteral(0), var(len)));

      addHavoc(var(ref));
      addAssume(isEqual(heapNewArray(
          context,
          var(HEAP_VAR),
          allocationType,
          var(len)), rval(var(ref))));
      addAssignment(var(HEAP_VAR), heapAddArray(
          context,
          var(HEAP_VAR),
          allocationType,
          var(len)));
    }

    public void visitNewArrayInstruction(NewArrayInstruction insn) {
      translateNewArrayInstruction(insn.getType());
    }

    public void visitANewArrayInstruction(ANewArrayInstruction insn) {
      translateNewArrayInstruction(insn.getType());
    }

    private BPLExpression buildMultiArrayAllocation(
        JArrayType type,
        int dimension,
        int lengthIdx) {
      if (dimension == 1) {
        return arrayAlloc(
            typeRef(type.getIndexedType()),
            var(intStackVar(lengthIdx)));
      } else {
        return multiArrayAlloc(
            typeRef(type.getIndexedType()),
            var(intStackVar(lengthIdx)),
            buildMultiArrayAllocation(
                (JArrayType) type.getIndexedType(),
                dimension - 1,
                lengthIdx + 1));
      }
    }

    public void visitMultiANewArrayInstruction(MultiANewArrayInstruction insn) {
      JArrayType type = insn.getType();
      int dims = insn.getDimensionCount();
      int first = handle.getFrame().getStackSize() - dims;
      String ref = refStackVar(first);

      BPLExpression[] vc = new BPLExpression[dims];
      for (int i = 0; i < dims; i++) {
        vc[i] = lessEqual(intLiteral(0), var(intStackVar(first + i)));
      }
      translateRuntimeException("java.lang.NegativeArraySizeException", vc);

      addHavoc(var(ref));
      addAssume(isEqual(heapNew(var(HEAP_VAR), buildMultiArrayAllocation(
          type,
          dims,
          first)), rval(var(ref))));
      addAssignment(
          var(HEAP_VAR),
          heapAdd(
              var(HEAP_VAR),
              buildMultiArrayAllocation(type, dims, first)
          )
      );
    }

    public void visitCheckCastInstruction(CheckCastInstruction insn) {
      String stackVar = refStackVar(handle.getFrame().getStackSize() - 1);
      BPLExpression type = typeRef(insn.getType());

      translateRuntimeException("java.lang.ClassCastException", isOfType(
          rval(var(stackVar)),
          type));
    }

    public void visitVCastInstruction(VCastInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      BPLExpression type = typeRef(insn.getTargetType());

      addAssignment(var(intStackVar(stack)), icast(
          var(intStackVar(stack)),
          type));
    }

    public void visitInstanceOfInstruction(InstanceOfInstruction insn) {
      int stack = handle.getFrame().getStackSize() - 1;
      BPLExpression type = typeRef(insn.getType());

      addAssignment(var(intStackVar(stack)), bool2int(isInstanceOf(
          rval(var(refStackVar(stack))),
          type)));
    }

    public void visitPopInstruction(PopInstruction insn) {
      // do nothing
    }

    public void visitPop2Instruction(Pop2Instruction insn) {
      // do nothing
    }

    public void visitSwapInstruction(SwapInstruction insn) {
      int stack1 = handle.getFrame().getStackSize() - 1;
      int stack2 = handle.getFrame().getStackSize() - 2;
      JType type = handle.getFrame().peek();
      addAssignment(var(swapVar(type)), var(stackVar(stack2, type)));
      addAssignment(var(stackVar(stack2, type)), var(stackVar(stack1, type)));
      addAssignment(var(stackVar(stack1, type)), var(swapVar(type)));
    }

    private void translateDupInstruction(int dupCount, int offset) {
      int top = handle.getFrame().getStackSize() - 1;
      for (int i = 0; i < offset; i++) {
        int from = top - i;
        int to = from + dupCount;
        JType type = handle.getFrame().peek(from);
        addAssignment(var(stackVar(to, type)), var(stackVar(from, type)));
      }
      if (dupCount < offset) {
        for (int i = 0; i < dupCount; i++) {
          int from = (top + dupCount) - i;
          int to = from - offset;
          JType type = handle.getFrame().peek(from - dupCount);
          addAssignment(var(stackVar(to, type)), var(stackVar(from, type)));
        }
      }
    }

    public void visitDupInstruction(DupInstruction insn) {
      translateDupInstruction(1, 1);
    }

    public void visitDup2Instruction(Dup2Instruction insn) {
      int stack1 = handle.getFrame().getStackSize() - 1;
      JType type1 = handle.getFrame().peek(stack1);
      if (type1.isCategory1CompType()) {
        translateDupInstruction(2, 2);
      } else {
        translateDupInstruction(1, 1);
      }
    }

    public void visitDupX1Instruction(DupX1Instruction insn) {
      translateDupInstruction(1, 2);
    }

    public void visitDupX2Instruction(DupX2Instruction insn) {
      int stack2 = handle.getFrame().getStackSize() - 2;
      JType type2 = handle.getFrame().peek(stack2);
      if (type2.isCategory1CompType()) {
        translateDupInstruction(1, 3);
      } else {
        translateDupInstruction(1, 2);
      }
    }

    public void visitDup2X1Instruction(Dup2X1Instruction insn) {
      int stack1 = handle.getFrame().getStackSize() - 1;
      JType type1 = handle.getFrame().peek(stack1);
      if (type1.isCategory1CompType()) {
        translateDupInstruction(2, 3);
      } else {
        translateDupInstruction(1, 2);
      }
    }

    public void visitDup2X2Instruction(Dup2X2Instruction insn) {
      int stack1 = handle.getFrame().getStackSize() - 1;
      int stack2 = handle.getFrame().getStackSize() - 2;
      JType type1 = handle.getFrame().peek(stack1);
      JType type2 = handle.getFrame().peek(stack2);
      if (!type1.isCategory1CompType() && !type2.isCategory1CompType()) {
        translateDupInstruction(1, 2);
      } else {
        int stack3 = handle.getFrame().getStackSize() - 3;
        JType type3 = handle.getFrame().peek(stack3);
        if (!type3.isCategory1CompType()) {
          translateDupInstruction(2, 3);
        } else if (!type1.isCategory1CompType()) {
          translateDupInstruction(1, 3);
        } else {
          translateDupInstruction(2, 4);
        }
      }
    }

    private void branchToHandlers(JType exception) {
      Set<String> labels = new LinkedHashSet<String>();
      boolean definitelyHandled = false;
      JType tightestHandlerType = JNullType.NULL;
      for (ExceptionHandler handler : method.getExceptionHandlers()) {
        if (handler.isActiveFor(handle)) {
          JType handlerType = handler.getType();
          if (exception.isSubtypeOf(handlerType)) {
            labels.add(handlerBlockLabel(cfgBlock, handlerType));
            definitelyHandled = true;
            break;
          } else if (handlerType.isSubtypeOf(exception)
              && tightestHandlerType.isProperSubtypeOf(handlerType)) {
            labels.add(handlerBlockLabel(cfgBlock, handlerType));
            tightestHandlerType = handlerType;
          }
        }
      }
      if (!definitelyHandled) {
        for (JClassType methodException : method.getExceptionTypes()) {
          if (exception.isSubtypeOf(methodException)
              || (methodException.isSubtypeOf(exception) && tightestHandlerType
                  .isProperSubtypeOf(methodException))) {
            labels.add(postXBlockLabel(methodException));
          }
        }
        if (labels.size() == 0) {
          labels.add(EXIT_BLOCK_LABEL);
        }
      }
      endBlock(labels.toArray(new String[labels.size()]));
    }

    /**
     * Translates a special BoogiePL block for all the exception handlers which
     * are reachable from the current instruction. The block assumes all the
     * type information which is guaranteed whenever the corresponding exception
     * handler is reached at runtime.
     */
    private void translateReachableExceptionHandlers() {
      ExceptionHandler[] handlers = method.getExceptionHandlers();
      for (int i = 0; i < handlers.length; i++) {
        ExceptionHandler handler = handlers[i];
        if (handler.isActiveFor(handle)) {
          InstructionHandle target = handler.getHandler();
          BasicBlock block = method.getCFG().findBlockStartingAt(target);
          // Check whether the exception handler is reachable from the
          // current basic block in the method's control flow graph.
          if ((block != null) && cfgBlock.isSuccessor(block)) {
            JType type = handler.getType();
            startBlock(handlerBlockLabel(cfgBlock, type));

            // addAssume(isExceptionalReturnState(var(RETURN_STATE_PARAM )));
            addAssignment(
                var(RETURN_STATE_PARAM),
                var(EXCEPTIONAL_RETURN_STATE));
            // Assume that the exception object is of the handler's exception
            // type.
            addAssume(isInstanceOf(rval(var(refStackVar(0))), typeRef(type)));
            // addAssume(isInstanceOf(rval(var(EXCEPTION_PARAM)),
            // typeRef(type)));

            // For any previous exception handler at the current instruction,
            // assume that the type of the exception object is not a subtype
            // of it since, otherwise, the exception would always be caught
            // by the previous handler.
            for (int j = 0; j < i; j++) {
              if (handlers[j].getType().isProperSubtypeOf(type)) {
                addAssume(logicalNot(isInstanceOf(
                    rval(var(refStackVar(0))),
                    typeRef(handlers[j].getType()))));
              }
            }

            // addAssignment(var(RETURN_VALUE_PARAM), var(refStackVar(0)));
            addAssignment(var(EXCEPTION_PARAM), var(refStackVar(0)));

            endBlock(cfgBlock.getSuccessorEdge(block));
          }
        }
      }
    }
  }
}
