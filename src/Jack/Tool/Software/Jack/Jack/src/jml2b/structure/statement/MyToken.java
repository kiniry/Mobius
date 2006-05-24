//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: MyToken.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

/**
 * This class defines tokens that are used to create expressions and statement
 * that does not exist as an output of the JML parser.
 * @author L. Burdy
 */
public interface MyToken {
    
    /**
     * The first token indice
     **/
	static final int FIRST_TOKEN = 367;
	
    /**
     * Token correspoding to a sequence of two statements
     **/
	static final int SEQUENCE = FIRST_TOKEN;
    
    /**
     * Token correspoding to a <code>skip</code>
     **/
	static final int SKIP = FIRST_TOKEN + 1;
    
    /**
     * Token correspoding to an obvious expression
     **/
	static final int BTRUE = FIRST_TOKEN + 2;
    
    /**
     * Token correspoding to a method call
     **/
	static final int METHOD_CALL = FIRST_TOKEN + 3;
    
    /**
     * Token correspoding to an array creation
     **/
	static final int NEWARRAY = FIRST_TOKEN + 4;
      
    /**
     * Token correspoding to a <i>called old</i>
     **/
    static final int T_CALLED_OLD = FIRST_TOKEN + 5;
    
    /** 
     * Token correspoding to a <i>fresh called old</i>
     **/
    static final int T_FRESH_CALLED_OLD = FIRST_TOKEN + 6;

	static final int T_VARIANT_OLD = FIRST_TOKEN + 7;

    /**
     * Array associating a string to a token
     **/
	static final String[] nodeString = { "", // 0;
		"EOF", // = 1;
		"", // 2;
		"NULL_TREE_LOOKAHEAD", // = 3;
		"ADDITIVE_ASSIGNMENT_OP", // = 4;
		"ADDITIVE_OP", // = 5;
		"BITWISE_OP", // = 6;
		"BITWISE_ASSIGNMENT_OP", // = 7;
		"EQUALITY_OP", // = 8;
		"LOGICAL_OP", // = 9;
		"MULTIPLICATIVE_ASSIGNMENT_OP", // = 10;
		"MULTIPLICATIVE_OP", // = 11;
		"RELATIONAL_OP", // = 12;
		"SHIFT_ASSIGNMENT_OP", // = 13;
		"SHIFT_OP", // = 14;
		"POST_INCREMENT_OP", // = 15;
		"PRE_INCREMENT_OP", // = 16;
		"UNARY_NUMERIC_OP", // = 17;
		"ACCESSIBLE_KEYWORD", // = 18;
		"AFFIRM_KEYWORD", // = 19;
		"ASSIGNABLE_KEYWORD", // = 20;
		"LOOP_ASSIGNABLE_KEYWORD", // = 21;
		"ASSUME_KEYWORD", // = 21;
		"HENCE_BY_KEYWORD", // = 22;
		"BREAKS_KEYWORD", // = 23;
		"CALLABLE_KEYWORD", // = 24;
		"CONSTRA-1, //_KEYWORD", // = 25;
		"CONTINUES_KEYWORD", // = 26;
		"DECREASING_KEYWORD", // = 27;
		"DEPENDS_KEYWORD", // = 28;
		"DIVERGES_KEYWORD", // = 29;
		"ENSURES_KEYWORD", // = 30;
		"EQUIVALENCE_OP", // = 31;
		"IMPLICATION_OP", // = 32;
		"INVARIANT_KEYWORD", // = 33;
		"JAVA_MODIFIER", // = 34;
		"JAVA_BUILTIN_TYPE", // = 35;
		"JML_MODIFIER", // = 36;
		"LETOLD_KEYWORD", // = 37;
		"MA-1, //AINING_KEYWORD", // = 38;
		"MEASURED_BY_KEYWORD", // = 39;
		"MODIFIER_SET", // = 40;
		"PRIVACY_MODIFIER", // = 41;
		"QUANTIFIER_TOKEN", // = 42;
		"REPRESENTS_KEYWORD", // = 43;
		"REQUIRES_KEYWORD", // = 44;
		"RETURNS_KEYWORD", // = 45;
		"SIGNALS_KEYWORD", // = 46;
		"WHEN_KEYWORD", // = 47;
		"ACCESSIBLE_SEQ", // = 48;
		"ARRAY_DECLARATOR", // = 49;
		"ASSERT", // = 50;
		"ASGNABLE_SEQ", // = 51;
		"LOOP_ASGNABLE_SEQ", //= 53;
		"BREAKS_SEQ", // = 52;
		"CALLABLE_SEQ", // = 53;
		"CASE", // = 54;
		"CAST", // = 55;
		"CONJOINABLE_SPEC", // = 56;
		"CONSTRUCTOR", // = 57;
		"CONT_SEQ", // = 58;
		"DIMS", // = 59;
		"DIM_EXPRS", // = 60;
		"DINFORMALLY", // = 61;
		"DIV_SEQ", // = 62;
		"DOC_ATSIGN", // = 63;
		"DOC_ATSIGN_KEYWORD", // = 64;
		"DOC_AUTHOR", // = 65;
		"DOC_COMMENT_START", // = 66;
		"DOC_DEPRECATED", // = 67;
		"DOC_EXCEPTION", // = 68;
		"DOC_JML_SPECS", // = 69;
		"DOC_NL_WS", // = 70;
		"DOC_NON_EMPTY_TEXTLINE", // = 71;
		"DOC_NON_NL_WS", // = 72;
		"DOC_PARAM", // = 73;
		"DOC_RETURN", // = 74;
		"DOC_SEE", // = 75;
		"DOC_SERIAL", // = 76;
		"DOC_SERIALDATA", // = 77;
		"DOC_SERIALFIELD", // = 78;
		"DOC_SINCE", // = 79;
		"DOC_THROWS", // = 80;
		"DOC_UNKNOWN_KEYWORD", // = 81;
		"DOC_VERSION", // = 82;
		"ENS_SEQ", // = 83;
		"EXT_ALSO", // = 84;
		"EXT_AND", // = 85;
		"FOR_INIT", // = 86;
		"FOR_TEST", // = 87;
		"FOR_UPDATER", // = 88;
		"INIT", // = 89;
		"INSTANCE_INIT", // = 90;
		"LOOP_INV_SEQ", // = 91;
		"METH", // = 92;
		"NESTED_CLASS", // = 93;
		"PARAM", // = 94;
		"POST_DEC", // = 95;
		"POST_INC", // = 96;
		"QUANTIFIED_EXPR", // = 97;
		"QUANT_VARS", // = 98;
		"REPLACE", // = 99;
		"RETURNS_SEQ", // = 100;
		"SET_COMPR", // = 101;
		"SIG_SEQ", // = 102;
		"LOOP_SIG_SEQ", // = 105;
		"SPEC_CASE", // = 103;
		"STAR_ELEMS", // = 104;
		"VAR_DECL", // = 105;
		"VF_SEQ", // = 106;
		"SPEC_STATEMENT", // 106bis
		"LITERAL_package", // = 107;
		"REFINE", // = 108;
		"MODEL", // = 109;
		"LITERAL_import", // = 110;
		"DOC_COMMENT", // = 111;
		"SEMI", // = 112;
		"IDENT", // = 113; Personal
		"DOT", // = 114; Personal
		"STAR", // = 115;
		"T_TYPEOFALLTYPES", // = 116;
		"LITERAL_private", // = 117;
		"LITERAL_public", // = 118;
		"LITERAL_protected", // = 119;
		"LITERAL_static", // = 120;
		"LITERAL_transient", // = 121;
		"LITERAL_final", // = 122;
		"LITERAL_abstract", // = 123;
		"LITERAL_native", // = 124;
		"LITERAL_synchronized", // = 125;
		"LITERAL_const", // = 126;
		"LITERAL_volatile", // = 127;
		"LITERAL_strictfp", // = 128;
		"LITERAL_class", // = 129;
		"LITERAL_extends", // = 130;
		"WEAKLY", // = 131;
		"LCURLY", // = 132;
		"RCURLY", // = 133;
		"LITERAL_-1, //erface", // = 134;
		"LITERAL_implements", // = 135;
		"COMMA", // = 136;
		"STATIC_INITIALIZER", // = 137;
		"INITIALIZER", // = 138;
		"LPAREN", // = 139;
		"RPAREN", // = 140;
		"LITERAL_throws", // = 141;
		"ASSIGN", // = 142;
		"L_ARROW", // = 143;
		"STRING_LITERAL", // = 144;
		"INITIALLY", // = 145;
		"READABLE_IF", // = 146;
		"MONITORED_BY", // = 147;
		"PURE", // = 148;
		"INSTANCE", // = 149;
		"SPEC_PUBLIC", // = 150;
		"SPEC_PROTECTED", // = 151;
		"MONITORED", // = 152;
		"UNINITIALIZED", // = 153;
		"GHOST", // = 154;
		"NON_NULL", // = 155;
		"INVARIANT", // = 156;
		"INVARIANT_REDUNDANTLY", // = 157;
		"CONSTRA-1, //", // = 158;
		"CONSTRA-1, //_REDUNDANTLY", // = 159;
		"FOR", // = 160;
		"T_EVERYTHING", // = 161;
		"LITERAL_super", // = 162;
		"LITERAL_this", // = 163;
		"T_OTHER", // = 164;
		"LITERAL_new", // = 165;
		"DEPENDS", // = 166;
		"DEPENDS_REDUNDANTLY", // = 167;
		"REPRESENTS", // = 168;
		"REPRESENTS_REDUNDANTLY", // = 169;
		"T_SUCH_THAT", // = 170;
		"AXIOM", // = 171;
		"LITERAL_void", // = 172;
		"ALSO", // = 173;
		"AND", // = 174;
		"BEHAVIOR", // = 175;
		"EXCEPTIONAL_BEHAVIOR", // = 176;
		"NORMAL_BEHAVIOR", // = 177;
		"FOR_EXAMPLE", // = 178;
		"EXAMPLE", // = 179;
		"EXCEPTIONAL_EXAMPLE", // = 180;
		"NORMAL_EXAMPLE", // = 181;
		"IMPLIES_THAT", // = 182;
		"SUBCLASSING_CONTRACT", // = 183;
		"ACCESSIBLE", // = 184;
		"ACCESSIBLE_REDUNDANTLY", // = 185;
		"LBRACK", // = 186;
		"RBRACK", // = 187;
		"CALLABLE", // = 188;
		"CALLABLE_REDUNDANTLY", // = 189;
		"LCURLY_VBAR", // = 190;
		"VBAR_RCURLY", // = 191;
		"MODEL_PROGRAM", // = 192;
		"FORALL", // = 193;
		"LET", // = 194;
		"OLD", // = 195;
		"REQUIRES", // = 196;
		"PRE", // = 197;
		"REQUIRES_REDUNDANTLY", // = 198;
		"PRE_REDUNDANTLY", // = 199;
		"T_NOT_SPECIFIED", // = 200;
		"WHEN", // = 201;
		"WHEN_REDUNDANTLY", // = 202;
		"MEASURED_BY", // = 203;
		"MEASURED_BY_REDUNDANTLY", // = 204;
		"LITERAL_if", // = 205;
		"LOOP_MODIFIES", // = 209;
		"ASSIGNABLE", // = 206;
		"MODIFIABLE", // = 207;
		"MODIFIES", // = 208;
		"ASSIGNABLE_REDUNDANTLY", // = 209;
		"MODIFIABLE_REDUNDANTLY", // = 210;
		"MODIFIES_REDUNDANTLY", // = 211;
		"T_FIELDS_OF", // = 212;
		"T_NOTHING", // = 213;
		"DOT_DOT", // = 214;
		"ENSURES", // = 215;
		"POST", // = 216;
		"ENSURES_REDUNDANTLY", // = 217;
		"POST_REDUNDANTLY", // = 218;
		"LOOP_EXSURES", // = 223;
		"SIGNALS", // = 219;
		"SIGNALS_REDUNDANTLY", // = 220;
		"EXSURES", // = 221;
		"EXSURES_REDUNDANTLY", // = 222;
		"DIVERGES", // = 223;
		"DIVERGES_REDUNDANTLY", // = 224;
		"COLON", // = 225;
		"LITERAL_else", // = 226;
		"LITERAL_while", // = 227;
		"LITERAL_do", // = 228;
		"LITERAL_for", // = 229;
		"LITERAL_break", // = 230;
		"LITERAL_continue", // = 231;
		"LITERAL_return", // = 232;
		"LITERAL_throw", // = 233;
		"LITERAL_switch", // = 234;
		"LITERAL_case", // = 235;
		"LITERAL_default", // = 236;
		"LITERAL_try", // = 237;
		"LITERAL_finally", // = 238;
		"LITERAL_catch", // = 239;
		"LITERAL_assert", // = 240;
		"HENCE_BY", // = 241;
		"HENCE_BY_REDUNDANTLY", // = 242;
		"ASSERT_REDUNDANTLY", // = 243;
		"ASSUME", // = 244;
		"ASSUME_REDUNDANTLY", // = 245;
		"SET", // = 246;
		"PLUS_ASSIGN", // = 247;
		"MINUS_ASSIGN", // = 248;
		"STAR_ASSIGN", // = 249;
		"DIV_ASSIGN", // = 250;
		"MOD_ASSIGN", // = 251;
		"SR_ASSIGN", // = 252;
		"BSR_ASSIGN", // = 253;
		"SL_ASSIGN", // = 254;
		"BAND_ASSIGN", // = 255;
		"BOR_ASSIGN", // = 256;
		"BXOR_ASSIGN", // = 257;
		"UNREACHABLE", // = 258;
		"CHOOSE", // = 259;
		"OR", // = 260;
		"CHOOSE_IF", // = 261;
		"ELSE", // = 262;
		"ABRUPT_BEHAVIOR", // = 263;
		"CONTINUES", // = 264;
		"CONTINUES_REDUNDANTLY", // = 265;
		"R_ARROW", // = 266;
		"BREAKS", // = 267;
		"BREAKS_REDUNDANTLY", // = 268;
		"RETURNS", // = 269;
		"RETURNS_REDUNDANTLY", // = 270;
		"MA-1, //AINING", // = 271;
		"MA-1, //AINING_REDUNDANTLY", // = 272;
		"LOOP_INVARIANT", // = 273;
		"LOOP_INVARIANT_REDUNDANTLY", // = 274;
		"DECREASING", // = 275;
		"DECREASING_REDUNDANTLY", // = 276;
		"DECREASES", // = 277;
		"DECREASES_REDUNDANTLY", // = 278;
		"QUESTION", // = 279;
		"EQUIV", // = 280;
		"NOT_EQUIV", // = 281;
		"LIMPLIES", // = 282;
		"BACKWARD_IMPLIES", // = 283;
		"LOR", // = 284;
		"LAND", // = 285;
		"BOR", // = 286;
		"BXOR", // = 287;
		"BAND", // = 288;
		"NOT_EQUAL", // = 289;
		"EQUAL", // = 290;
		"LT", // = 291;
		"GT", // = 292;
		"LE", // = 293;
		"GE", // = 294;
		"IS_SUBTYPE_OF", // = 295;
		"LITERAL_instanceof", // = 296;
		"SL", // = 297;
		"SR", // = 298;
		"BSR", // = 299;
		"PLUS", // = 300;
		"MINUS", // = 301;
		"DIV", // = 302;
		"MOD", // = 303;
		"INC", // = 304;
		"DEC", // = 305;
		"BNOT", // = 306;
		"LNOT", // = 307;
		"LITERAL_true", // = 308;
		"LITERAL_false", // = 309;
		"LITERAL_null", // = 310;
		"T_LBLNEG", // = 311;
		"T_LBLPOS", // = 312;
		"T_RESULT", // = 313;
		"T_OLD", // = 314; Personal
		"T_NOT_MODIFIED", // = 315;
		"T_FRESH", // = 316;
		"T_REACH", // = 317;
		"T_NONNULLELEMENTS", // = 318;
		"T_TYPEOF", // = 319;
		"T_ELEMTYPE", // = 320;
		"T_TYPE", // = 321;
		"T_LOCKSET", // = 322;
		"T_IS_INITIALIZED", // = 323;
		"T_INVARIANT_FOR", // = 324;
		"INFORMAL_DESCRIPTION", // = 325;
		"LITERAL_boolean", // = 326;
		"LITERAL_byte", // = 327;
		"LITERAL_char", // = 328;
		"LITERAL_short", // = 329;
		"LITERAL_int, //", // = 330;
		"LITERAL_long", // = 331;
		"LITERAL_float", // = 332;
		"LITERAL_double", // = 333;
		"NUM_INT", // = 334; personal
		"CHAR_LITERAL", // = 335;
		"NUM_FLOAT", // = 336;
		"T_FORALL", // = 337;
		"T_EXISTS", // = 338;
		"T_MAX", // = 339;
		"T_MIN", // = 340;
		"T_SUM", // = 341;
		"T_PRODUCT", // = 342;
		"T_NUM_OF", // = 343;
		"SPEC_SL_COMMENT", // = 344;
		"SL_COMMENT", // = 345;
		"NON_NL_WS", // = 346;
		"NL_WS", // = 347;
		"IGNORED_AT_IN_COMMENT", // = 348;
		"ML_COMMENT", // = 349;
		"WS", // = 350;
		"NOWARN_LABEL", // = 351;
		"NOWARN_LABEL_LIST", // = 352;
		"JML_BACKSLASH_SEQUENCE", // = 353;
		"ESC", // = 354;
		"HEX_DIGIT", // = 355;
		"VOCAB", // = 356;
		"EXPONENT", // = 357;
		"FLOAT_SUFFIX", // = 358;
		"BADCHAR", // = 359;
		"SEQUENCE             ", // = 360;
		"SKIP                 ", // = 361;
		"BTRUE                ", // = 362;
		"METHOD_CALL          ", // = 363;
        "NEW_ARRAY            ",
		"B_APPLICATION        ", // = 370; Personal
        "T_CALLED_OLD         ",
        "T_FRESH_CALLED_OLD   ",
        "T_VARIANT_OLD        "};
}