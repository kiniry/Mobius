package b2bpl.translation;


public interface TranslationConstants {

  String CONSTRUCTOR_NAME = ".init";

  String CLASS_INITIALIZER_NAME = ".clinit";

  String GLOBAL_VAR_PREFIX = "$";

  String VALUE_TYPE_PREFIX = "$";

  String FUNC_PREFIX = "";

  String HEAP_TYPE =         "Store";

  String LOCATION_TYPE =     "Location";

  String ALLOCATION_TYPE =   "Allocation";
  
  String RETURN_STATE_TYPE = "ReturnState";

  String HEAP_VAR     = "heap";

  String OLD_HEAP_VAR = "old_heap";

  String PRE_HEAP_VAR = "pre_heap";

  String LOOP_HEAP_VAR_PREFIX = "loop_heap";

  String LOOP_VARIANT_VAR_PREFIX = "loop_variant";

  String VALUE_TYPE = "Value";

  String RESULT_VAR = "result";

  String INT_TYPE_ABBREV = "_i";

  String REF_TYPE_ABBREV = "_r";

  String PARAM_VAR_PREFIX = "param";

  String LOCAL_VAR_PREFIX = "reg";

  String STACK_VAR_PREFIX = "stack";

  // String CALL_RESULT_VAR_PREFIX = "callResult";
  
  // String THIS_VAR = "this";
  
  String NORMAL_RETURN_STATE =      "normal";
  
  String EXCEPTIONAL_RETURN_STATE = "exceptional";

  String RETURN_STATE_VAR = "rs";
  
  String RETURN_VALUE_VAR = "rv";
  
  String EXCEPTION_VAR    = "ex";
  
  String RETURN_HEAP_PARAM =  "retheap";
  
  String RETURN_STATE_PARAM = "retstate";
  
  String RETURN_VALUE_PARAM = "retvalue";
  
  String EXCEPTION_PARAM    = "exception";

  String INT_CALL_RESULT_VAR = /* CALL_RESULT_VAR_PREFIX */ RETURN_VALUE_VAR + INT_TYPE_ABBREV;

  String REF_CALL_RESULT_VAR = /* CALL_RESULT_VAR_PREFIX */ RETURN_VALUE_VAR + REF_TYPE_ABBREV;

  String SWAP_VAR_PREFIX = "swap";

  String INT_SWAP_VAR = SWAP_VAR_PREFIX + INT_TYPE_ABBREV;

  String REF_SWAP_VAR = SWAP_VAR_PREFIX + REF_TYPE_ABBREV;

  String BOOL2INT_FUNC = FUNC_PREFIX + "bool2int";

  String INT2BOOL_FUNC = FUNC_PREFIX + "int2bool";

  String SHL_FUNC = FUNC_PREFIX +  "shl";

  String SHR_FUNC = FUNC_PREFIX +  "shr";

  String USHR_FUNC = FUNC_PREFIX + "ushr";

  String AND_FUNC = FUNC_PREFIX +  "and";

  String OR_FUNC = FUNC_PREFIX +   "or";

  String XOR_FUNC = FUNC_PREFIX +  "xor";
  
  String AND_OP = "&&";
  
  String OR_OP =  "||";

  String IS_CLASS_TYPE_FUNC = FUNC_PREFIX + "isClassType";

  String IS_VALUE_TYPE_FUNC = FUNC_PREFIX + "isValueType";

  String IS_ARRAY_TYPE_FUNC = FUNC_PREFIX + "isArrayType";
  
  String IS_NORMAL_RETURN_STATE_FUNC = FUNC_PREFIX + "isNormalReturnState";
  
  String IS_EXCEPTIONAL_RETURN_STATE_FUNC = FUNC_PREFIX + "isExceptionalReturnState";

  String INV_FUNC = FUNC_PREFIX + "inv";

  String FIELD_TYPE_FUNC = FUNC_PREFIX + "fieldType";

  String FIELD_LOC_FUNC = FUNC_PREFIX + "fieldLoc";

  String ARRAY_LOC_FUNC = FUNC_PREFIX + "arrayLoc";

  String OBJ_FUNC = FUNC_PREFIX + "obj";

  String ARRAY_LENGTH_FUNC = FUNC_PREFIX + "arrayLength";

  String ARRAY_TYPE_FUNC = FUNC_PREFIX + "arrayType";

  String ELEMENT_TYPE_FUNC = FUNC_PREFIX + "elementType";

  String TYPE_OBJECT_FUNC = FUNC_PREFIX + "typeObject";

  String OBJECT_ALLOC_FUNC = FUNC_PREFIX + "objectAlloc";

  String ARRAY_ALLOC_FUNC = FUNC_PREFIX + "arrayAlloc";

  String MULTI_ARRAY_ALLOC_FUNC = FUNC_PREFIX + "multiArrayAlloc";

  String IS_NEW_MULTI_ARRAY_FUNC = FUNC_PREFIX + "isNewMultiArray";

  String MULTI_ARRAY_PARENT_FUNC = FUNC_PREFIX + "multiArrayParent";

  String MULTI_ARRAY_POSITION_FUNC = FUNC_PREFIX + "multiArrayPosition";

  String GET_FUNC = FUNC_PREFIX + "get";

  String UPDATE_FUNC = FUNC_PREFIX + "update";

  String ALIVE_FUNC = FUNC_PREFIX + "alive";

  String NEW_FUNC = FUNC_PREFIX + "new";

  String ADD_FUNC = FUNC_PREFIX + "add";

  String TOINT_FUNC = FUNC_PREFIX + "toint";

  String TOREF_FUNC = FUNC_PREFIX + "toref";

  String IVAL_FUNC = FUNC_PREFIX + "ival";

  String RVAL_FUNC = FUNC_PREFIX + "rval";

  String INIT_FUNC = FUNC_PREFIX + "init";

  String STATIC_FUNC = FUNC_PREFIX + "static";

  String TYP_FUNC = FUNC_PREFIX + "typ";

  String LTYP_FUNC = FUNC_PREFIX + "ltyp";

  String ALLOC_TYPE_FUNC = FUNC_PREFIX + "allocType";

  String IS_OF_TYPE_FUNC = FUNC_PREFIX + "isOfType";

  String IS_INSTANCE_OF_FUNC = FUNC_PREFIX + "isInstanceOf";

  String IS_IN_RANGE_FUNC = FUNC_PREFIX + "isInRange";

  String ICAST_FUNC = FUNC_PREFIX + "icast";

  String IF_THEN_ELSE_FUNC = FUNC_PREFIX + "ifThenElse";

  String BLOCK_LABEL_PREFIX = "block_";

  String INIT_BLOCK_LABEL = "init";

  String PRE_BLOCK_LABEL = "pre";

  String POST_BLOCK_LABEL= "post";
  
  String EXCEPTION_HANDLERS_LABEL = "exception_handlers";

  String POSTX_BLOCK_LABEL_PREFIX = "postX_";

  String EXIT_BLOCK_LABEL = "exit";

  String LOOP_BLOCK_LABEL_SUFFIX = "_Loop";

  String TRUE_BLOCK_LABEL_SUFFIX = "_True";

  String FALSE_BLOCK_LABEL_SUFFIX = "_False";

  String CASE_BLOCK_LABEL_SUFFIX = "_Case";

  String DEFAULT_BLOCK_LABEL_SUFFIX = "_Default";

  String NO_EXCEPTION_BLOCK_LABEL_SUFFIX = "_Normal";

  String EXCEPTION_BLOCK_LABEL_SUFFIX = "_X_#";

  String RUNTIME_EXCEPTION_TRUE_BLOCK_LABEL_SUFFIX = "_RT_X_True_#";

  String RUNTIME_EXCEPTION_FALSE_BLOCK_LABEL_SUFFIX = "_RT_X_False_#";

  String HANDLER_BLOCK_LABEL_SUFFIX = "_Handler_#";

  String STRING_LITERAL_PREFIX = GLOBAL_VAR_PREFIX + "stringLiteral";

  String INT_LITERAL_PREFIX = GLOBAL_VAR_PREFIX + "int#";

  String CLASS_LITERAL_SUFFIX = ".class";
}
