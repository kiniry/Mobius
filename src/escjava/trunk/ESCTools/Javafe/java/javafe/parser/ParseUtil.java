/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser;

import javafe.ast.*;
import javafe.util.StackVector;
import javafe.util.Location;
import javafe.util.ErrorSet;

/**
 * Base class for Java parser.
 *
 * @see javafe.ast.ASTNode
 * @see javafe.parser.ParseType
 * @see javafe.parser.Parse
 */

public class ParseUtil
{
    public ParseUtil() {
	//@ set seqModifierPragma.elementType = \type(ModifierPragma)
	//@ set seqModifierPragma.owner = this
    }


    //----------------------- Misc Helper Functions ----------------------------

    /** Raises a <TT>RuntimeException</TT> with the argument string. */

    //@ ensures false
    private static void fail(String m) { ErrorSet.fatal(m); }

    //@ requires loc != Location.NULL
    //@ ensures false
    public static void fail(int loc, String m) { ErrorSet.fatal(loc, m); }

    /** 
     Takes an expected token from the input stream, 
     calls <TT>fail</TT> on error.
     */
    //@ requires l != null && l.m_in != null
    //@ modifies l.ttype, l.auxVal, l.identifierVal
    //@ ensures \old(l.ttype)==expected
    public void expect(Lex l, int expected) {
        if( l.ttype != expected ) 
            fail(l.startingLoc,
                 "Unexpected token '" + PrettyPrint.inst.toString(l.ttype) +
                 "', expected '" + PrettyPrint.inst.toString(expected)+"'");
        l.getNextToken();
    }

    /**

     Converts operator tokens to corresponding AST tag.
     Tokens INC and DEC get mapped to PREFIXINC and PREFIXDEC

     */

    int operatorTokenToTag(int token) {
        // Right now we have the identity mapping.
        return token;
    }


    /*------------------------ Modifiers -------------------------------*/

    //* Internal working storage for parse*Modifier* functions
    //@ invariant seqModifierPragma.elementType == \type(ModifierPragma)
    //@ invariant seqModifierPragma.owner == this
    protected final StackVector seqModifierPragma = new StackVector();

    /**
     * Keyword at index i in this array corresponds to bit i in
     * modifier bitset.  Thus PRIVATE is at index 1, ACC_PRIVATE =
     * 1<<1.
     */
    public static final int modifierKeywords[] = {
	TagConstants.PUBLIC, TagConstants.PRIVATE, TagConstants.PROTECTED, 
	TagConstants.STATIC, TagConstants.FINAL, 
	TagConstants.SYNCHRONIZED, TagConstants.VOLATILE,
	TagConstants.TRANSIENT, TagConstants.NATIVE, TagConstants.NATIVE,
	TagConstants.ABSTRACT, TagConstants.STRICT
    };


    /**
     * Parse a list of modifier pragmas.  Returns <code>null</code> if
     * <code>l</code> does not point to a modifier pragma.  Otherwise,
     * reads <code>l</code> until there are no more modifier pragmas and
     * returns the resulting list.
     */
    //@ requires l.m_in != null
    public ModifierPragmaVec parseModifierPragmas(/*@non_null*/ Lex l) {
	if (l.ttype != TagConstants.MODIFIERPRAGMA)
	    return null;

	seqModifierPragma.push();
	do {
	    seqModifierPragma.addElement(l.auxVal);
	    l.getNextToken();
	} while (l.ttype == TagConstants.MODIFIERPRAGMA);
	return ModifierPragmaVec.popFromStackVector(seqModifierPragma);
    }

    /**
     * Parse a list of modifier pragmas and adds them to an existing
     * <code>ModifierPragmaVec</code>.  If the existing
     * <code>ModifierPragmaVec</code> was <code>null</code>, then it
     * either returns <code>null</code> (if <code>l</code> does not point
     * to a modifier pragma), or returns a new
     * <code>ModifierPragmaVec</code>.
     */
    //@ requires l.m_in != null
    public ModifierPragmaVec parseMoreModifierPragmas(/*@non_null*/ Lex l, 
						      ModifierPragmaVec orig)
    {
	ModifierPragmaVec modifierPragmas = parseModifierPragmas( l );
	if (modifierPragmas == null)
	    return orig;
	else if (orig == null)
	    return modifierPragmas;
	else {
	    orig.append( modifierPragmas );
	    return orig;
	}
    }

    /** As a side effect, <code>parseModifiers</code> mutates this
     value. */
    public ModifierPragmaVec modifierPragmas;


    /**
     * Parse a list of modifiers.  Ensures no duplicate Java modifiers
     * and only one
     * of the access modifiers public, protected, private.  Return
     * integer encoding the Java modifiers.
     *
     * <p> In addition to parsing Java modifiers, also handles pragma
     * parsers.  If no pragma parsers are seen, sets
     * <c>modifierPragmas</c> to <c>null</c>.  Otherwise, sets it to be
     * the list of modifier pragmas seen.
     *
     * @see javafe.ast.ModifierConstants
     */
    //@ requires l.m_in != null
    //@ modifies modifierPragmas
    public int parseModifiers(/*@non_null*/ Lex l) {
        boolean seenPragma = false;
        int modifiers = Modifiers.NONE;

        getModifierLoop:
        for(;;) {
            if (l.ttype == TagConstants.MODIFIERPRAGMA) {
                if (! seenPragma) { seqModifierPragma.push(); seenPragma = true; }
                seqModifierPragma.addElement(l.auxVal);
                l.getNextToken();
                continue getModifierLoop;
            } else for( int i=0; i<modifierKeywords.length; i++ ) {
                if( l.ttype == modifierKeywords[i] ) {
                    // Token is modifier keyword 
                    int modifierBit = 1<<i;
                    if( (modifiers & modifierBit) != 0 ) {
                        fail(l.startingLoc, "Duplicate occurrence of modifier '"
                             +PrettyPrint.inst.toString(l.ttype)+"'");
                    }
                    if( (modifiers & Modifiers.ACCESS_MODIFIERS) != 0 &&
                        (modifierBit & Modifiers.ACCESS_MODIFIERS) != 0 ) {
                        fail(l.startingLoc, 
                             "Cannot have more than one of the access modifiers "+
                             "public, protected, private");
                    }
                    modifiers |= modifierBit;
                    l.getNextToken();
                    continue getModifierLoop;
                }
            }
            // Next token is not a modifier

            if (! seenPragma)
                modifierPragmas = null;
            else
                modifierPragmas
                    = ModifierPragmaVec.popFromStackVector(seqModifierPragma);
            return modifiers;
        }
    }
}
