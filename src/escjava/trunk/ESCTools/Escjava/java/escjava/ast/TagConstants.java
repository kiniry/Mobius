/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;

import javafe.ast.Identifier;
import javafe.util.Assert;

import escjava.prover.Atom;

public class TagConstants extends javafe.tc.TagConstants
    implements GeneratedTags
{
    //// Tags for new binary operators
    public static final int IMPLIES = escjava.ast.GeneratedTags.LAST_TAG + 1;
    public static final int EXPLIES = IMPLIES + 1;
    public static final int IFF = EXPLIES + 1;  // equivalence (equality)
    public static final int NIFF = IFF + 1;     // discrepance (xor)
    public static final int SUBTYPE = NIFF + 1;
    public static final int DOTDOT = SUBTYPE + 1;

    //// Tags for pragma punctuation
    public static final int JML_LEFTARROW = DOTDOT + 1; // <-
    public static final int JML_RIGHTARROW = JML_LEFTARROW + 1; // ->
    public static final int JML_OPENPRAGMA = JML_RIGHTARROW + 1; // {|
    public static final int JML_CLOSEPRAGMA = JML_OPENPRAGMA + 1; // |}

    //// Tags for new literal expressions
    public static final int SYMBOLLIT = JML_CLOSEPRAGMA + 1;

    //// Tags for new primitive types
    public static final int ANY = SYMBOLLIT + 1;
    public static final int TYPECODE = ANY + 1;
    public static final int LOCKSET = TYPECODE + 1;
    
    //// Tags for guarded commands
    public static final int ASSERTCMD = LOCKSET + 1;
    public static final int ASSUMECMD = ASSERTCMD + 1;
    public static final int CHOOSECMD = ASSUMECMD + 1;
    public static final int RAISECMD = CHOOSECMD + 1;
    public static final int SKIPCMD = RAISECMD + 1;
    public static final int TRYCMD = SKIPCMD + 1;

    //// Tags for special tokens
    public static final int INFORMALPRED_TOKEN = TRYCMD + 1;

    //// Tags for ESCJ keywords
    public static final int FIRSTESCKEYWORDTAG = INFORMALPRED_TOKEN + 1;
    public static final int ALSO_ENSURES = FIRSTESCKEYWORDTAG;
    public static final int ALSO_EXSURES = ALSO_ENSURES + 1;
    public static final int ALSO_MODIFIES = ALSO_EXSURES + 1;
    public static final int ALSO_REQUIRES = ALSO_MODIFIES + 1;
    public static final int ASSUME = ALSO_REQUIRES + 1;
    public static final int AXIOM = ASSUME + 1;
    public static final int DECREASES = AXIOM + 1;
    public static final int DTTFSA = DECREASES + 1;
    public static final int ENSURES = DTTFSA + 1;
    public static final int ELEMSNONNULL = ENSURES + 1; // Function
    public static final int ELEMTYPE = ELEMSNONNULL + 1; // Function
    public static final int EXISTS = ELEMTYPE + 1;
    public static final int EXSURES = EXISTS + 1;
    public static final int FRESH = EXSURES + 1; // Non-GCE function
    public static final int FORALL = FRESH + 1;
    public static final int GHOST = FORALL + 1;
    public static final int HELPER = GHOST + 1;
    public static final int INVARIANT = HELPER + 1;
    public static final int LBLPOS = INVARIANT + 1;
    public static final int LBLNEG = LBLPOS + 1;
    public static final int LOOP_INVARIANT = LBLNEG + 1;
    public static final int LOOP_PREDICATE = LOOP_INVARIANT + 1;
    public static final int LS = LOOP_PREDICATE + 1;
    public static final int MAX = LS + 1; // Function
    public static final int MODIFIES = MAX + 1;
    public static final int MONITORED = MODIFIES + 1;
    public static final int MONITORED_BY = MONITORED + 1;
    public static final int NON_NULL = MONITORED_BY + 1;
    public static final int NOWARN = NON_NULL + 1;
    public static final int PRE = NOWARN + 1;
    public static final int READABLE_IF = PRE + 1;
    public static final int RES = READABLE_IF + 1;
    public static final int REQUIRES = RES + 1;
    public static final int SET = REQUIRES + 1;
    public static final int SPEC_PUBLIC = SET + 1;
    public static final int STILL_DEFERRED = SPEC_PUBLIC + 1;
    public static final int TYPE = STILL_DEFERRED + 1;	// "type"
    public static final int TYPETYPE = TYPE + 1;	  // "TYPE"; name for TYPECODE
    public static final int TYPEOF = TYPETYPE + 1; // Function
    public static final int UNINITIALIZED = TYPEOF + 1;
    public static final int UNREACHABLE = UNINITIALIZED + 1;
    public static final int WRITABLE_DEFERRED = UNREACHABLE + 1;
    public static final int WRITABLE_IF = WRITABLE_DEFERRED+ 1;
    public static final int SKOLEM_CONSTANT = WRITABLE_IF + 1;
    public static final int LASTESCKEYWORDTAG = SKOLEM_CONSTANT;

    //// Tags for ESC/Java checks
    public static final int FIRSTESCCHECKTAG = LASTESCKEYWORDTAG + 1;
    public static final int CHKARITHMETIC = FIRSTESCCHECKTAG;
    public static final int CHKARRAYSTORE = CHKARITHMETIC + 1;
    public static final int CHKASSERT = CHKARRAYSTORE + 1;
    public static final int CHKCLASSCAST = CHKASSERT + 1;
    public static final int CHKCODEREACHABILITY = CHKCLASSCAST + 1;
    public static final int CHKCONSTRUCTORLEAK = CHKCODEREACHABILITY + 1;
    public static final int CHKDECREASES_BOUND = CHKCONSTRUCTORLEAK + 1;
    public static final int CHKDECREASES_DECR = CHKDECREASES_BOUND + 1;
    public static final int CHKDEFINEDNESS = CHKDECREASES_DECR + 1;
    public static final int CHKINDEXNEGATIVE = CHKDEFINEDNESS + 1;
    public static final int CHKINDEXTOOBIG = CHKINDEXNEGATIVE + 1;
    public static final int CHKINITIALIZATION = CHKINDEXTOOBIG + 1;
    public static final int CHKINITIALIZERLEAK = CHKINITIALIZATION + 1;
    public static final int CHKLOCKINGORDER = CHKINITIALIZERLEAK + 1;
    public static final int CHKLOOPINVARIANT = CHKLOCKINGORDER + 1;
    public static final int CHKLOOPOBJECTINVARIANT = CHKLOOPINVARIANT + 1;
    public static final int CHKMODIFIESEXTENSION = CHKLOOPOBJECTINVARIANT + 1;
    public static final int CHKMODIFIES = CHKMODIFIESEXTENSION + 1;
    public static final int CHKNEGATIVEARRAYSIZE = CHKMODIFIES + 1;
    public static final int CHKNONNULL = CHKNEGATIVEARRAYSIZE + 1;
    public static final int CHKNONNULLINIT = CHKNONNULL + 1;
    public static final int CHKNONNULLRESULT = CHKNONNULLINIT + 1;
    public static final int CHKNULLPOINTER = CHKNONNULLRESULT + 1;
    public static final int CHKOBJECTINVARIANT = CHKNULLPOINTER + 1;
    public static final int CHKOWNERNULL = CHKOBJECTINVARIANT + 1;
    public static final int CHKPOSTCONDITION = CHKOWNERNULL + 1;
    public static final int CHKPRECONDITION = CHKPOSTCONDITION + 1;
    public static final int CHKSHARING = CHKPRECONDITION + 1;
    public static final int CHKUNENFORCEBLEOBJECTINVARIANT = CHKSHARING + 1;
    public static final int CHKUNEXPECTEDEXCEPTION = CHKUNENFORCEBLEOBJECTINVARIANT + 1;
    public static final int CHKWRITABLEDEFERRED = CHKUNEXPECTEDEXCEPTION + 1;
    public static final int CHKWRITABLE = CHKWRITABLEDEFERRED + 1;
    public static final int CHKFREE = CHKWRITABLE + 1;
    public static final int LASTESCCHECKTAG = CHKFREE;

    //// Tags for Nary function symbols that are _not_ ESCJ keywords
    //
    // These need to be added both below and in escfunctions in this file,
    // as well as as switch labels in escjava.ast.EscPrettyPrint and
    // escjava.translate.VcToString.
    //
    public static final int FIRSTFUNCTIONTAG = LASTESCCHECKTAG + 1;
    public static final int ALLOCLT = FIRSTFUNCTIONTAG;
    public static final int ALLOCLE = ALLOCLT+1;
    public static final int ANYEQ = ALLOCLE+1;
    public static final int ANYNE = ANYEQ+1;
    public static final int ARRAYLENGTH = ANYNE+1;
    public static final int ARRAYFRESH = ARRAYLENGTH + 1;
    public static final int ARRAYSHAPEMORE = ARRAYFRESH + 1;
    public static final int ARRAYSHAPEONE = ARRAYSHAPEMORE + 1;
    public static final int ASELEMS = ARRAYSHAPEONE + 1;
    public static final int ASFIELD = ASELEMS + 1;
    public static final int ASLOCKSET = ASFIELD + 1;
    public static final int BOOLAND = ASLOCKSET + 1;
    public static final int BOOLEQ = BOOLAND + 1;
    public static final int BOOLIMPLIES = BOOLEQ + 1;
    public static final int BOOLNE = BOOLIMPLIES + 1;
    public static final int BOOLNOT = BOOLNE + 1;
    public static final int BOOLOR = BOOLNOT + 1;
    public static final int CAST = BOOLOR + 1;
    public static final int CLASSLITERALFUNC = CAST + 1;
    public static final int CONDITIONAL = CLASSLITERALFUNC + 1;
    public static final int ECLOSEDTIME = CONDITIONAL + 1;
    // ELEMSNONNULL -- an ESC keyword
    // ELEMTYPE -- an ESC keyword
    public static final int FCLOSEDTIME = ECLOSEDTIME + 1;
    public static final int FLOATINGADD = FCLOSEDTIME + 1;
    public static final int FLOATINGDIV = FLOATINGADD + 1;
    public static final int FLOATINGEQ = FLOATINGDIV + 1;
    public static final int FLOATINGGE = FLOATINGEQ + 1;
    public static final int FLOATINGGT = FLOATINGGE + 1;
    public static final int FLOATINGLE = FLOATINGGT + 1;
    public static final int FLOATINGLT = FLOATINGLE + 1;
    public static final int FLOATINGMOD = FLOATINGLT + 1;
    public static final int FLOATINGMUL = FLOATINGMOD + 1;
    public static final int FLOATINGNE = FLOATINGMUL + 1;
    public static final int FLOATINGNEG = FLOATINGNE + 1;
    public static final int FLOATINGSUB = FLOATINGNEG + 1;
    public static final int INTEGRALADD = FLOATINGSUB + 1;
    public static final int INTEGRALAND = INTEGRALADD + 1;
    public static final int INTEGRALDIV = INTEGRALAND + 1;
    public static final int INTEGRALEQ = INTEGRALDIV + 1;
    public static final int INTEGRALGE = INTEGRALEQ + 1;
    public static final int INTEGRALGT = INTEGRALGE + 1;
    public static final int INTEGRALLE = INTEGRALGT + 1;
    public static final int INTEGRALLT = INTEGRALLE + 1;
    public static final int INTEGRALMOD = INTEGRALLT + 1;
    public static final int INTEGRALMUL = INTEGRALMOD + 1;
    public static final int INTEGRALNE = INTEGRALMUL + 1;
    public static final int INTEGRALNEG = INTEGRALNE + 1;
    public static final int INTEGRALNOT = INTEGRALNEG + 1;
    public static final int INTEGRALOR = INTEGRALNOT + 1;
    public static final int INTSHIFTL = INTEGRALOR + 1;
    public static final int LONGSHIFTL = INTSHIFTL + 1;
    public static final int INTSHIFTR = LONGSHIFTL + 1;
    public static final int LONGSHIFTR = INTSHIFTR + 1;
    public static final int INTSHIFTRU = LONGSHIFTR + 1;
    public static final int LONGSHIFTRU = INTSHIFTRU + 1;
    public static final int INTEGRALSUB = LONGSHIFTRU + 1;
    public static final int INTEGRALXOR = INTEGRALSUB + 1;
    public static final int IS = INTEGRALXOR + 1;
    public static final int ISALLOCATED = IS + 1;
    public static final int ISNEWARRAY = ISALLOCATED + 1;
    // MAX -- an ESC keyword
    public static final int LOCKLE = ISNEWARRAY + 1;
    public static final int LOCKLT = LOCKLE + 1;
    public static final int METHODCALL = LOCKLT + 1;
    public static final int REFEQ = METHODCALL + 1;
    public static final int REFNE = REFEQ + 1;
    public static final int SELECT = REFNE + 1;
    public static final int STORE = SELECT + 1;
    public static final int STRINGCAT = STORE + 1;
    public static final int TYPEEQ = STRINGCAT + 1; 
    public static final int TYPENE = TYPEEQ + 1; 
    public static final int TYPELE = TYPENE + 1; // a.k.a. "<:"
    // TYPEOF -- an ESC keyword
    public static final int VALLOCTIME = TYPELE + 1;
    public static final int LASTFUNCTIONTAG = VALLOCTIME;

    // Constants used in deciding how to translate CHKs
    public static final int CHK_AS_ASSUME = LASTFUNCTIONTAG + 1;
    public static final int CHK_AS_ASSERT = CHK_AS_ASSUME + 1;
    public static final int CHK_AS_SKIP = CHK_AS_ASSERT + 1;

    //// JML keywords
    public static final int FIRSTJMLKEYWORDTAG = CHK_AS_SKIP + 1;

    public static final int JML_WACK_DURATION = FIRSTJMLKEYWORDTAG;
    // \elemtype -- an ESC keyword
    public static final int JML_EVERYTHING = JML_WACK_DURATION + 1;
    // \exists -- an ESC keyword
    public static final int JML_FIELDS_OF = JML_EVERYTHING + 1;
    // \forall -- an ESC keyword
    // \fresh -- an ESC keyword 
    public static final int JML_INVARIANT_FOR = JML_FIELDS_OF + 1;
    public static final int JML_IS_INITIALIZED = JML_INVARIANT_FOR + 1;
    // \lblneg -- an ESC keyword
    // \lblpos -- an ESC keyword
    // \lockset -- an ESC keyword
    // \max -- an ESC keyword 
    public static final int JML_MIN = JML_IS_INITIALIZED + 1;
    // \nonnullelements -- an ESC keyword
    public static final int JML_NOTHING = JML_MIN + 1;
    public static final int JML_NOT_MODIFIED = JML_NOTHING + 1;
    public static final int JML_NOT_SPECIFIED = JML_NOT_MODIFIED + 1;
    public static final int JML_NUM_OF = JML_NOT_SPECIFIED + 1;
    // \old -- an ESC keyword
    public static final int JML_OTHER = JML_NUM_OF + 1;
    public static final int JML_PRIVATE_DATA = JML_OTHER + 1;
    public static final int JML_PRODUCT = JML_PRIVATE_DATA + 1;
    public static final int JML_REACH = JML_PRODUCT + 1;
    // \result -- an ESC keyword
    public static final int JML_SPACE = JML_REACH + 1;
    public static final int JML_SUCH_THAT = JML_SPACE + 1;
    public static final int JML_SUM = JML_SUCH_THAT + 1;
    // \type -- an ESC keyword
    // \typeof -- an ESC keyword
    // \TYPE -- an ESC keyword
    public static final int JML_WACK_WORKING_SPACE = JML_SUM + 1;

    public static final int JML_ABRUPT_BEHAVIOR = JML_WACK_WORKING_SPACE + 1;
    public static final int JML_ACCESSIBLE_REDUNDANTLY = JML_ABRUPT_BEHAVIOR + 1;
    public static final int JML_ACCESSIBLE = JML_ACCESSIBLE_REDUNDANTLY + 1;
    public static final int JML_ALSO = JML_ACCESSIBLE + 1;
    public static final int JML_ASSERT_REDUNDANTLY = JML_ALSO + 1;
    public static final int JML_ASSIGNABLE_REDUNDANTLY = JML_ASSERT_REDUNDANTLY + 1;
    public static final int JML_ASSIGNABLE = JML_ASSIGNABLE_REDUNDANTLY + 1;
    public static final int JML_ASSUME_REDUNDANTLY = JML_ASSIGNABLE + 1;
    // assume -- an ESC keyword
    // axiom -- an ESC keyword
    public static final int JML_BEHAVIOR = JML_ASSUME_REDUNDANTLY + 1;
    public static final int JML_BREAKS_REDUNDANTLY = JML_BEHAVIOR + 1;
    public static final int JML_BREAKS = JML_BREAKS_REDUNDANTLY + 1;
    public static final int JML_CALLABLE_REDUNDANTLY = JML_BREAKS + 1;
    public static final int JML_CALLABLE = JML_CALLABLE_REDUNDANTLY + 1;
    public static final int JML_CHOOSE_IF = JML_CALLABLE + 1;
    public static final int JML_CHOOSE = JML_CHOOSE_IF + 1;
    public static final int JML_CONSTRAINT_REDUNDANTLY = JML_CHOOSE + 1;
    public static final int JML_CONSTRAINT = JML_CONSTRAINT_REDUNDANTLY + 1;
    public static final int JML_CONTINUES_REDUNDANTLY = JML_CONSTRAINT + 1;
    public static final int JML_CONTINUES = JML_CONTINUES_REDUNDANTLY + 1; // @review
    public static final int JML_DECREASES_REDUNDANTLY = JML_CONTINUES + 1;
    // decreases -- an ESC keyword
    public static final int JML_DECREASING_REDUNDANTLY = JML_DECREASES_REDUNDANTLY + 1;
    public static final int JML_DECREASING = JML_DECREASING_REDUNDANTLY + 1;
    public static final int JML_DEPENDS_REDUNDANTLY = JML_DECREASING + 1;
    public static final int JML_DEPENDS = JML_DEPENDS_REDUNDANTLY + 1;
    public static final int JML_DIVERGES_REDUNDANTLY = JML_DEPENDS + 1;
    public static final int JML_DIVERGES = JML_DIVERGES_REDUNDANTLY + 1;
    public static final int JML_DURATION_REDUNDANTLY = JML_DIVERGES + 1;
    public static final int JML_DURATION = JML_DURATION_REDUNDANTLY + 1;
    public static final int JML_ENSURES_REDUNDANTLY = JML_DURATION + 1;
    // ensures -- an ESC keyword
    public static final int JML_EXAMPLE = JML_ENSURES_REDUNDANTLY + 1;
    public static final int JML_EXCEPTIONAL_BEHAVIOR = JML_EXAMPLE + 1;
    public static final int JML_EXCEPTIONAL_EXAMPLE = JML_EXCEPTIONAL_BEHAVIOR + 1;
    public static final int JML_EXSURES_REDUNDANTLY = JML_EXCEPTIONAL_EXAMPLE + 1;
    // exsures -- an ESC keyword
    public static final int JML_FORALL = JML_EXSURES_REDUNDANTLY + 1;
    public static final int JML_FOR_EXAMPLE = JML_FORALL + 1;
    // ghost -- an ESC keyword
    public static final int JML_IMPLIES_THAT = JML_FOR_EXAMPLE + 1;
    // helper -- an ESC keyword
    public static final int JML_HENCE_BY_REDUNDANTLY = JML_IMPLIES_THAT + 1;
    public static final int JML_HENCE_BY = JML_HENCE_BY_REDUNDANTLY + 1;
    public static final int JML_INITIALIZER = JML_HENCE_BY + 1;
    public static final int JML_INITIALLY = JML_INITIALIZER + 1;
    public static final int JML_INSTANCE = JML_INITIALLY + 1;
    public static final int JML_INVARIANT_REDUNDANTLY = JML_INSTANCE + 1;
    // invariant -- an ESC keyword
    public static final int JML_LOOP_INVARIANT_REDUNDANTLY = JML_INVARIANT_REDUNDANTLY + 1;
    // loop_invariant -- an ESC keyword
    public static final int JML_MAINTAINING_REDUNDANTLY = JML_LOOP_INVARIANT_REDUNDANTLY + 1;
    public static final int JML_MAINTAINING = JML_MAINTAINING_REDUNDANTLY + 1;
    public static final int JML_MEASURED_BY_REDUNDANTLY = JML_MAINTAINING + 1;
    public static final int JML_MEASURED_BY = JML_MEASURED_BY_REDUNDANTLY + 1;
    public static final int JML_MODEL = JML_MEASURED_BY + 1;
    public static final int JML_MODEL_PROGRAM = JML_MODEL + 1;
    public static final int JML_MODIFIABLE_REDUNDANTLY = JML_MODEL_PROGRAM + 1;
    public static final int JML_MODIFIABLE = JML_MODIFIABLE_REDUNDANTLY + 1;
    public static final int JML_MODIFIES_REDUNDANTLY = JML_MODIFIABLE + 1;
    // modifies -- an ESC keyword
    // monitored_by -- an ESC keyword
    // monitored -- an ESC keyword
    // non_null -- an ESC keyword
    public static final int JML_NORMAL_BEHAVIOR = JML_MODIFIES_REDUNDANTLY + 1;
    public static final int JML_NORMAL_EXAMPLE = JML_NORMAL_BEHAVIOR + 1;
    // nowarn -- an ESC keyword
    public static final int JML_OLD = JML_NORMAL_EXAMPLE + 1;
    public static final int JML_OR = JML_OLD + 1;
    public static final int JML_POST_REDUNDANTLY = JML_OR + 1;
    public static final int JML_POST = JML_POST_REDUNDANTLY + 1;
    public static final int JML_PRE_REDUNDANTLY = JML_POST + 1;
    public static final int JML_PRE = JML_PRE_REDUNDANTLY + 1;
    public static final int JML_PURE = JML_PRE + 1;
    // readable_if -- an ESC keyword
    public static final int JML_REFINE = JML_PURE + 1;
    public static final int JML_REPRESENTS_REDUNDANTLY = JML_REFINE + 1;
    public static final int JML_REPRESENTS = JML_REPRESENTS_REDUNDANTLY + 1;
    public static final int JML_REQUIRES_REDUNDANTLY = JML_REPRESENTS + 1;
    // requires -- an ESC keyword
    public static final int JML_RETURNS_REDUNDANTLY = JML_REQUIRES_REDUNDANTLY + 1;
    public static final int JML_RETURNS = JML_RETURNS_REDUNDANTLY + 1;
    // set -- an ESC keyword
    public static final int JML_SIGNALS_REDUNDANTLY = JML_RETURNS + 1;
    public static final int JML_SIGNALS = JML_SIGNALS_REDUNDANTLY + 1;
    public static final int JML_SPEC_PROTECTED = JML_SIGNALS + 1;
    // spec_public -- an ESC keyword
    public static final int JML_STATIC_INITIALIZER = JML_SPEC_PROTECTED + 1;
    public static final int JML_SUBCLASSING_CONTRACT = JML_STATIC_INITIALIZER + 1;
    // uninitialized -- an ESC keyword
    // unreachable -- an ESC keyword
    public static final int JML_WEAKLY = JML_SUBCLASSING_CONTRACT + 1;
    public static final int JML_WHEN_REDUNDANTLY = JML_WEAKLY + 1;
    public static final int JML_WHEN = JML_WHEN_REDUNDANTLY + 1;
    public static final int JML_WORKING_SPACE_REDUNDANTLY = JML_WHEN + 1;
    public static final int JML_WORKING_SPACE = JML_WORKING_SPACE_REDUNDANTLY + 1;

    public static final int LASTJMLKEYWORDTAG = JML_WORKING_SPACE;

    public static final int LAST_TAG = LASTJMLKEYWORDTAG;

    public static final Identifier ExsuresIdnName = 
        Identifier.intern("Optional..Exsures..Id..Name");

    //// Helper functions

    public static String toVcString(int tag) {
        switch(tag) {
            case TYPECODE:
                return "TYPECODE";		// displayed to user as "TYPE"
            default:
                break;
        }

        String s = toString(tag);
        //@ assume toString.length > 0;
        if (s.charAt(0) == '\\') {
            s = s.substring(1);
        }
        if (s.equals("lockset")) {
            s = "LS";
        } else if (s.equals("result")) {
            s = "RES";
        }
        return s;
    }

    // Documented in parent.

    public static String toString(int tag) {
        switch(tag) {
            // new literal expression (not true keyword)
            case  SYMBOLLIT:
                return "*SYMBOLLIT*";
            // guarded commands (not true keywords)
            case ASSERTCMD:
                return "*ASSERTCMD*";
            case ASSUMECMD:
                return "*ASSUMECMD*";
            case CHOOSECMD:
                return "*CHOOSECMD*";
            case RAISECMD:
                return "*RAISECMD*";
            case SKIPCMD:
                return "*SKIPCMD*";
            case TRYCMD:
                return "*TRYCMD*";
            // informal predicates (not true keyword)
            case INFORMALPRED_TOKEN:
                return "*INFORMAL_PREDICATE*";
            // special symbols
            case IMPLIES:
                return "==>";
            case EXPLIES:
                return "<==";
            case IFF:
                return "<==>";
            case NIFF:
                return "<=!=>";
            case SUBTYPE:
                return "<:";
	    case DOTDOT:
		return "..";
	    case JML_LEFTARROW:
		return "<-";
	    case JML_RIGHTARROW:
		return "->";
	    case JML_OPENPRAGMA:
		return "{|";
	    case JML_CLOSEPRAGMA:
		return "|}";
            case ANY:
                return "ANY";
            case TYPECODE:
                //return "TYPECODE";		// displayed to user as "TYPE"
                return "TYPE";
            case LOCKSET:
                return "LOCKSET";
            case CHK_AS_ASSUME:
                return "CHK_AS_ASSUME";
            case CHK_AS_ASSERT:
                return "CHK_AS_ASSERT";
            case CHK_AS_SKIP:
                return "CHK_AS_SKIP";
            default:
                if (FIRSTESCKEYWORDTAG <= tag && tag <= LASTESCKEYWORDTAG)
                    return esckeywords[tag - FIRSTESCKEYWORDTAG].toString();
                else if (FIRSTESCCHECKTAG <= tag && tag <= LASTESCCHECKTAG)
                    return escchecks[tag - FIRSTESCCHECKTAG];
                else if (FIRSTFUNCTIONTAG <= tag && tag <= LASTFUNCTIONTAG)
                    return escfunctions[tag - FIRSTFUNCTIONTAG];
                else if (FIRSTJMLKEYWORDTAG <= tag && tag <= LASTJMLKEYWORDTAG)
                    return jmlkeywords[tag - FIRSTJMLKEYWORDTAG].toString();
                else if (tag <= javafe.tc.TagConstants.LAST_TAG)
                    return javafe.tc.TagConstants.toString(tag);
                else {
                    return "Unknown ESC tag <" + tag
                        + " (+" + (tag - javafe.tc.TagConstants.LAST_TAG) + ") >";
                }
        }
    }

    /**
     * @param keyword the keyword to lookup.
     * @return the index of the {@link TagConstants} attribute
     * corresponding to the keyword encoded as an {@link Identifier}
     * in the parameter 'keyword'. A {@link #NULL} is returned if
     * the identifier in question is not an ESC/Java or JML keyword
     * known to {@link TagConstants}.
     */
    public static int fromIdentifier(Identifier keyword) {
        for(int i = 0; i < esckeywords.length; i++)
            if (keyword == esckeywords[i]) return i + FIRSTESCKEYWORDTAG;
        for(int i = 0; i < jmlkeywords.length; i++)
            if (keyword == jmlkeywords[i]) return i + FIRSTJMLKEYWORDTAG;
        return NULL;
    }

    public static int checkFromString(String s) {
        for (int i = FIRSTESCCHECKTAG; i <= LASTESCCHECKTAG; i++) {
            if (s.equals(escchecks[i - FIRSTESCCHECKTAG]))
                return i;
        }
        //@ unreachable
        Assert.fail("unrecognized check string: \"" + s + "\"");
        return -1;
    }

    /**
     * @return a "redundant-fied" version of the passed tag if it can
     * be made redundant; otherwise, return the parameter unchanged.
     */
    public static int makeRedundant(int tag) {
        int Result = tag;
        switch (tag) {
	    case TagConstants.REQUIRES:
                Result = TagConstants.JML_REQUIRES_REDUNDANTLY; break;
            case TagConstants.ENSURES:
                Result = TagConstants.JML_ENSURES_REDUNDANTLY; break;
            case TagConstants.JML_PRE:
                Result = TagConstants.JML_PRE_REDUNDANTLY; break;
            case TagConstants.JML_DIVERGES:
                Result = TagConstants.JML_DIVERGES_REDUNDANTLY; break;
            case TagConstants.JML_WHEN:
                Result = TagConstants.JML_WHEN_REDUNDANTLY; break;
            case TagConstants.JML_POST:
                Result = TagConstants.JML_POST_REDUNDANTLY; break;
            case TagConstants.EXSURES:
                Result = TagConstants.JML_EXSURES_REDUNDANTLY; break;
            case TagConstants.JML_SIGNALS:
                Result = TagConstants.JML_SIGNALS_REDUNDANTLY; break;
            case TagConstants.JML_MODIFIABLE:
                Result = TagConstants.JML_MODIFIABLE_REDUNDANTLY; break;
            case TagConstants.JML_ASSIGNABLE:
                Result = TagConstants.JML_ASSIGNABLE_REDUNDANTLY; break;
            case TagConstants.MODIFIES:
                Result = TagConstants.JML_MODIFIES_REDUNDANTLY; break;
            case TagConstants.JML_MEASURED_BY:
                Result = TagConstants.JML_MEASURED_BY_REDUNDANTLY; break;
            case TagConstants.ASSERT:
                Result = TagConstants.JML_ASSERT_REDUNDANTLY; break;
            case TagConstants.ASSUME:
                Result = TagConstants.JML_ASSUME_REDUNDANTLY; break;
            case TagConstants.LOOP_INVARIANT:
                Result = TagConstants.JML_LOOP_INVARIANT_REDUNDANTLY; break;
            case TagConstants.JML_MAINTAINING:
                Result = TagConstants.JML_MAINTAINING_REDUNDANTLY; break;
            case TagConstants.DECREASES:
                Result = TagConstants.JML_DECREASES_REDUNDANTLY; break;
            case TagConstants.INVARIANT:
                Result = TagConstants.JML_INVARIANT_REDUNDANTLY; break;
            case TagConstants.JML_CONSTRAINT:
                Result = TagConstants.JML_CONSTRAINT_REDUNDANTLY; break;
            case TagConstants.JML_DECREASING:
                Result = TagConstants.JML_DECREASING_REDUNDANTLY; break;
            case TagConstants.JML_DURATION:
                Result = TagConstants.JML_DURATION_REDUNDANTLY; break;
            case TagConstants.JML_WORKING_SPACE:
                Result = TagConstants.JML_WORKING_SPACE_REDUNDANTLY; break;
        }
        return Result;
    }
    
    /**
     * @return an "unredundant-fied" version of the passed tag if it
     * is redundant; otherwise, return the parameter unchanged.
     */
    public static int unRedundant(int tag) {
        int Result = tag;
        switch (tag) {
	    case TagConstants.JML_REQUIRES_REDUNDANTLY:
                Result = TagConstants.REQUIRES; break;
            case TagConstants.JML_ENSURES_REDUNDANTLY:
                Result = TagConstants.ENSURES; break;
            case TagConstants.JML_PRE_REDUNDANTLY:
                Result = TagConstants.JML_PRE; break;
            case TagConstants.JML_DIVERGES_REDUNDANTLY:
                Result = TagConstants.JML_DIVERGES; break;
            case TagConstants.JML_WHEN_REDUNDANTLY:
                Result = TagConstants.JML_WHEN; break;
            case TagConstants.JML_POST_REDUNDANTLY:
                Result = TagConstants.JML_POST; break;
            case TagConstants.JML_EXSURES_REDUNDANTLY:
                Result = TagConstants.EXSURES; break;
            case TagConstants.JML_SIGNALS_REDUNDANTLY:
                Result = TagConstants.JML_SIGNALS; break;
            case TagConstants.JML_MODIFIABLE_REDUNDANTLY:
                Result = TagConstants.JML_MODIFIABLE; break;
            case TagConstants.JML_ASSIGNABLE_REDUNDANTLY:
                Result = TagConstants.JML_ASSIGNABLE; break;
            case TagConstants.JML_MODIFIES_REDUNDANTLY:
                Result = TagConstants.MODIFIES; break;
            case TagConstants.JML_MEASURED_BY_REDUNDANTLY:
                Result = TagConstants.JML_MEASURED_BY; break;
            case TagConstants.JML_ASSERT_REDUNDANTLY:
                Result = TagConstants.ASSERT; break;
            case TagConstants.JML_ASSUME_REDUNDANTLY:
                Result = TagConstants.ASSUME; break;
            case TagConstants.JML_LOOP_INVARIANT_REDUNDANTLY:
                Result = TagConstants.LOOP_INVARIANT; break;
            case TagConstants.JML_MAINTAINING_REDUNDANTLY:
                Result = TagConstants.JML_MAINTAINING; break;
            case TagConstants.JML_DECREASES_REDUNDANTLY:
                Result = TagConstants.DECREASES; break;
            case TagConstants.JML_INVARIANT_REDUNDANTLY:
                Result = TagConstants.INVARIANT; break;
            case TagConstants.JML_CONSTRAINT_REDUNDANTLY:
                Result = TagConstants.JML_CONSTRAINT; break;
            case TagConstants.JML_DECREASING_REDUNDANTLY:
                Result = TagConstants.JML_DECREASING; break;
            case TagConstants.JML_DURATION_REDUNDANTLY:
                Result = TagConstants.JML_DURATION; break;
            case TagConstants.JML_WORKING_SPACE_REDUNDANTLY:
                Result = TagConstants.JML_WORKING_SPACE; break;
        }
        return Result;
    }

    public static boolean isRedundant(int tag) {
	return (tag == TagConstants.JML_REQUIRES_REDUNDANTLY) ||
            (tag == TagConstants.JML_ENSURES_REDUNDANTLY) ||
            (tag == TagConstants.JML_PRE_REDUNDANTLY) ||
            (tag == TagConstants.JML_DIVERGES_REDUNDANTLY) ||
            (tag == TagConstants.JML_WHEN_REDUNDANTLY) ||
            (tag == TagConstants.JML_POST_REDUNDANTLY) ||
            (tag == TagConstants.JML_EXSURES_REDUNDANTLY) ||
            (tag == TagConstants.JML_SIGNALS_REDUNDANTLY) ||
            (tag == TagConstants.JML_DURATION_REDUNDANTLY) ||
            (tag == TagConstants.JML_WORKING_SPACE_REDUNDANTLY) ||
            tag == TagConstants.JML_MODIFIABLE_REDUNDANTLY ||
            tag == TagConstants.JML_ASSIGNABLE_REDUNDANTLY ||
            tag == TagConstants.JML_MODIFIES_REDUNDANTLY ||
            tag == TagConstants.JML_MEASURED_BY_REDUNDANTLY ||
            tag == TagConstants.JML_ASSERT_REDUNDANTLY ||
            tag == TagConstants.JML_ASSUME_REDUNDANTLY ||
            tag == TagConstants.JML_LOOP_INVARIANT_REDUNDANTLY ||
            tag == TagConstants.JML_MAINTAINING_REDUNDANTLY ||
            tag == TagConstants.JML_DECREASES_REDUNDANTLY ||
            tag == TagConstants.JML_INVARIANT_REDUNDANTLY ||
            tag == TagConstants.JML_CONSTRAINT_REDUNDANTLY ||
            tag == TagConstants.JML_DECREASING_REDUNDANTLY;
    }

    private static Identifier[] esckeywords = {
        Identifier.intern("also_ensures"),
        Identifier.intern("also_exsures"),
        Identifier.intern("also_modifies"),
        Identifier.intern("also_requires"),
        Identifier.intern("assume"),
        Identifier.intern("axiom"),
        Identifier.intern("decreases"),
        Identifier.intern("\\dttfsa"),
        Identifier.intern("ensures"),
        Identifier.intern("\\nonnullelements"),
        Identifier.intern("\\elemtype"),
        Identifier.intern("\\exists"),
        Identifier.intern("exsures"),
        Identifier.intern("\\fresh"),
        Identifier.intern("\\forall"),
        Identifier.intern("ghost"),
        Identifier.intern("helper"),
        Identifier.intern("invariant"),
        Identifier.intern("\\lblpos"),
        Identifier.intern("\\lblneg"),
        Identifier.intern("loop_invariant"),
        Identifier.intern("loop_predicate"),
        Identifier.intern("\\lockset"),
        Identifier.intern("\\max"),
        Identifier.intern("modifies"),
        Identifier.intern("monitored"),
        Identifier.intern("monitored_by"),
        Identifier.intern("non_null"),
        Identifier.intern("nowarn"),
        Identifier.intern("\\old"),  // TagConstants.PRE
        Identifier.intern("readable_if"),
        Identifier.intern("\\result"),
        Identifier.intern("requires"),
        Identifier.intern("set"),
        Identifier.intern("spec_public"),
        Identifier.intern("still_deferred"),
        Identifier.intern("\\type"),			// TYPE
        Identifier.intern("\\TYPE"),			// TYPETYPE
        Identifier.intern("\\typeof"),
        Identifier.intern("uninitialized"),
        Identifier.intern("unreachable"),
        Identifier.intern("writable_deferred"),
        Identifier.intern("writable_if"),
        Identifier.intern("skolem_constant")
    };

    private static String[] escchecks = {
        "ZeroDiv",
        "ArrayStore",
        "Assert",
        "Cast",
        "Reachable",
        "CLeak",
        "DecreasesBound",
        "Decreases",
        "Unreadable",
        "IndexNegative",
        "IndexTooBig",
        "Uninit",
        "ILeak",
        "Deadlock",
        "LoopInv",
        "LoopObjInv",
        "ModExt",
        "Modifies",
        "NegSize",
        "NonNull",
        "NonNullInit",
        "NonNullResult",
        "Null",
        "Invariant",
        "OwnerNull",
        "Post",
        "Pre",
        "Race",
        "Unenforcable",
        "Exception",
        "Deferred",
        "Writable",
        "Free"  // printed in debugging output only
    };
        
    private static String[] escfunctions = {
        "allocLT",
        "allocLE",
        "anyEQ",
        "anyNE",
        "arrayLength",
        "arrayFresh",
        "arrayShapeMore",
        "arrayShapeOne",
        "asElems",
        "asField",
        "asLockSet",
        "boolAnd",
        "boolEq",
        "boolImplies",
        "boolNE",
        "boolNot",
        "boolOr",
        "cast",
        "classLiteral",
        "termConditional",
        "eClosedTime",
        "fClosedTime",
        "floatingAdd",
        "floatingDiv",
        "floatingEQ",
        "floatingGE",
        "floatingGT",
        "floatingLE",
        "floatingLT",
        "floatingMod",
        "floatingMul",
        "floatingNE",
        "floatingNeg",
        "floatingSub",
        "integralAdd",
        "integralAnd",
        "integralDiv",
        "integralEQ",
        "integralGE",
        "integralGT",
        "integralLE",
        "integralLT",
        "integralMod",
        "integralMul",
        "integralNE",
        "integralNeg",
        "integralNot",
        "integralOr",
        "intShiftL",
        "longShiftL",
        "intShiftAR",
        "longShiftAR",
        "intShiftUR",
        "longShiftUR",
        "integralSub",
        "integralXor",
        "is",
        "isAllocated",
        "isNewArray",
        "lockLE",
        "lockLT",
	"methodCall",
        "refEQ",
        "refNE",
        "select",
        "store",
        "stringCat",
        "typeEQ",
        "typeNE",
        "typeLE",
        "vAllocTime"
    };

    private static Identifier[] jmlkeywords = {
        Identifier.intern("\\duration"),
        Identifier.intern("\\everything"),
        Identifier.intern("\\fields_of"),
        Identifier.intern("\\invariant_for"),
        Identifier.intern("\\is_initialized"),
        Identifier.intern("\\min"),
        Identifier.intern("\\nothing"),
        Identifier.intern("\\not_modified"),
        Identifier.intern("\\not_specified"),
        Identifier.intern("\\num_of"),
        Identifier.intern("\\other"),
        Identifier.intern("\\private_data"),
        Identifier.intern("\\product"),
        Identifier.intern("\\reach"),
        Identifier.intern("\\space"),
        Identifier.intern("\\such_that"),
        Identifier.intern("\\sum"),
        Identifier.intern("\\working_space"),
        Identifier.intern("abrupt_behavior"),
        Identifier.intern("accessible_redundantly"),
        Identifier.intern("accessible"),
        Identifier.intern("also"),
        Identifier.intern("assert_redundantly"),
        Identifier.intern("assignable_redundantly"),
        Identifier.intern("assignable"),
        Identifier.intern("assume_redundantly"),
        Identifier.intern("behavior"),
        Identifier.intern("breaks_redundantly"),
        Identifier.intern("breaks"),
        Identifier.intern("callable_redundantly"),
        Identifier.intern("callable"),
        Identifier.intern("choose_if"),
        Identifier.intern("choose"),
        Identifier.intern("constraint_redundantly"),
        Identifier.intern("constraint"),
        Identifier.intern("continues_redundantly"),
        Identifier.intern("continues"),
        Identifier.intern("decreases_redundantly"),
        Identifier.intern("decreasing_redundantly"),
        Identifier.intern("decreasing"),
        Identifier.intern("depends_redundantly"),
        Identifier.intern("depends"),
        Identifier.intern("diverges_redundantly"),
        Identifier.intern("diverges"),
        Identifier.intern("duration_redundantly"),
        Identifier.intern("duration"),
        Identifier.intern("ensures_redundantly"),
        Identifier.intern("example"),
        Identifier.intern("exceptional_behavior"),
        Identifier.intern("exceptional_example"),
        Identifier.intern("exsures_redundantly"),
        Identifier.intern("forall"),
        Identifier.intern("for_example"),
        Identifier.intern("implies_that"),
        Identifier.intern("hence_by_redundantly"),
        Identifier.intern("hence_by"),
        Identifier.intern("initializer"),
        Identifier.intern("initially"),
        Identifier.intern("instance"),
        Identifier.intern("invariant_redundantly"),
        Identifier.intern("loop_invariant_redundantly"),
        Identifier.intern("maintaining_redundantly"),
        Identifier.intern("maintaining"),
        Identifier.intern("measured_by_redundantly"),
        Identifier.intern("measured_by"),
        Identifier.intern("model"),
        Identifier.intern("model_program"),
        Identifier.intern("modifiable_redundantly"),
        Identifier.intern("modifiable"),
        Identifier.intern("modifies_redundantly"),
        Identifier.intern("normal_behavior"),
        Identifier.intern("normal_example"),
        Identifier.intern("old"),
        Identifier.intern("or"),
        Identifier.intern("post_redundantly"),
        Identifier.intern("post"),
        Identifier.intern("pre_redundantly"),
        Identifier.intern("pre"), // JML_PRE not PRE (which is \old )
        Identifier.intern("pure"),
        Identifier.intern("refine"),
        Identifier.intern("represents_redundantly"),
        Identifier.intern("represents"),
        Identifier.intern("requires_redundantly"),
        Identifier.intern("returns_redundantly"),
        Identifier.intern("returns"),
        Identifier.intern("signals_redundantly"),
        Identifier.intern("signals"),
        Identifier.intern("spec_protected"),
        Identifier.intern("static_initializer"),
        Identifier.intern("subclassing_contract"),
        Identifier.intern("weakly"),
        Identifier.intern("when_redundantly"),
        Identifier.intern("when"),
        Identifier.intern("working_space_redundantly"),
        Identifier.intern("working_space")
    };

    public static void main(String[] args) {
        for(int i = FIRST_TAG; i <= LAST_TAG; i++ )
            System.out.println(i + " " + toString(i));
    }
}
