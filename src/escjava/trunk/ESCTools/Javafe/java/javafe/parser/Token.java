/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser;

import javafe.ast.Identifier;
import javafe.ast.LexicalPragma;
import javafe.ast.ModifierPragma;
import javafe.ast.StmtPragma;
import javafe.ast.TypeDeclElemPragma;
import javafe.ast.PrettyPrint;

import javafe.util.Assert;
import javafe.util.Location;

/**
 * The <code>Token</code> class defines a set of fields that describe
 * lexical tokens.
 *
 * <p> Allocating an individual <code>Token</code> object for every
 * token consumes a lot of memory.  Instead, our front end tries to
 * reuse <code>Token</code> instances as much as possible.  Thus, for
 * example, <code>Lex</code> is a subclass of <code>Token</code>;
 * <code>Lex</code> returns information about the current token not by
 * allocating a new <code>Token</code> object but rather by filling in
 * the <code>Token</code> fields of itself.  To facilitate the reuse
 * of <code>Token</code> instances, <code>Token</code> has a
 * <code>copyInto</code> method.
 */

public class Token
{
    /***************************************************
     *                                                 *
     * Instance fields:				       *
     *                                                 *
     **************************************************/

    /**
     * Integer code giving the kind of token.<p>
     *
     * To clear a token, set this field to Token.CLEAR and set
     * identifierVal and auxVal to null, as is done in the
     * clear() method.
     *
     * @see javafe.parser.TagConstants
     */
    public int ttype = CLEAR;

    //* The token code to use to clear a token; EOF for now.
    public static final int CLEAR = TagConstants.EOF;

    public void clear() {
        ttype = CLEAR;
        identifierVal = null;
        auxVal = null;
    }

    /** The location of the first character of the token. */
    //@ invariant startingLoc != Location.NULL
    public int startingLoc;

    /**
     * The location of the last character of the token.  (This value
     * isn't "off-by-one" right now.)
     */
    //@ invariant endingLoc != Location.NULL
    public int endingLoc;


    /**
     * Identifier represented by the token.  Must be non-null if
     * <code>ttype</code> is <TT>TagConstants.IDENT</TT>.
     */
    /*@ invariant (ttype==TagConstants.IDENT) ==> (identifierVal != null) */
    public Identifier identifierVal;

    /**
     * Auxillary information about the token.  In the case of literal
     * tokens, this field holds the value of token.  In particular,
     * if <code>ttype</code> is one of the codes on the left of the
     * following table, then <code>auxVal</code> must be an instance
     * of the class on the right:
     *
     * <center><code><table>
     *    <tr><td> TagConstants.INTLIT </td>    <td> Integer </td></tr>
     *    <tr><td> TagConstants.LONGLIT </td>   <td> Long </td></tr>
     *    <tr><td> TagConstants.FLOATLIT </td>  <td> Float </td></tr>
     *    <tr><td> TagConstants.DOUBLELIT </td> <td> Double </td></tr>
     *    <tr><td> TagConstants.STRINGLIT </td> <td> String </td></tr>
     *    <tr><td> TagConstants.CHARLIT </td>   <td> Integer </td></tr>
     *    <tr><td> TagConstants.LEXICALPRAGMA </td>
     *                                <td> LexicalPragma </td></tr>
     *    <tr><td> TagConstants.MODIFIERPRAGMA </td>
     *                                <td> ModifierPragma </td></tr>
     *    <tr><td> TagConstants.STMTPRAGMA </td> <td> StmtPragma </td></tr>
     *    <tr><td> TagConstants.TYPEDECLELEMPRAGMA </td>
     *                                <td> TypeDeclElemPragma</td></tr>
     * </table> </code> </center><p>
     *
     * For the various pragmas, <code>auxVal</code> may be
     * <code>null</code>, but for the literals it may <em>not</em>
     * be.
     */
    /*@ invariant (
     !(ttype==TagConstants.BOOLEANLIT) &&
     (ttype==TagConstants.INTLIT ==> auxVal instanceof Integer) &&
     (ttype==TagConstants.LONGLIT ==> auxVal instanceof Long) &&
     (ttype==TagConstants.FLOATLIT ==> auxVal instanceof Float) &&
     (ttype==TagConstants.DOUBLELIT ==> auxVal instanceof Double) &&
     (ttype==TagConstants.STRINGLIT ==> auxVal instanceof String) &&
     (ttype==TagConstants.CHARLIT ==> auxVal instanceof Integer) &&
     (ttype==TagConstants.LEXICALPRAGMA ==> auxVal instanceof
     LexicalPragma) &&
     (ttype==TagConstants.MODIFIERPRAGMA ==> auxVal instanceof
     ModifierPragma) &&
     (ttype==TagConstants.STMTPRAGMA ==> auxVal instanceof StmtPragma) &&
     (ttype==TagConstants.TYPEDECLELEMPRAGMA ==> auxVal instanceof
     TypeDeclElemPragma) &&
     (ttype==TagConstants.TYPEMODIFIERPRAGMA ==> auxVal instanceof
     TypeModifierPragma)
     ) */
    public Object auxVal;


    /***************************************************
     *                                                 *
     * Creation:				       *
     *                                                 *
     **************************************************/

    /*
     * This is not really safe since violates invariants... !!!!
     *
     * NOTE: This is not a helper; we use invalid tokens in TokenQueue and
     *       Lex.savedState.
     */
    public Token() {}	//@ nowarn Invariant  // produces invalid Token


    /**
     * Copy all the fields of <code>this</code> into
     * <code>dst</code>.  For convenience, returns <code>dst</code>.
     */
    public final Token copyInto(/*@ non_null @*/ Token dst) {
	dst.ttype = ttype;
	dst.startingLoc = startingLoc;
	dst.endingLoc = endingLoc;
	dst.identifierVal = identifierVal;
	dst.auxVal = auxVal;
	return dst;
    }


    /***************************************************
     *                                                 *
     * Operations:				       *
     *                                                 *
     **************************************************/

    /**
     * Return a representation of <code>this</code> suitable for debug
     * output.
     */
    public String ztoString() {
        String result = Location.toFileName(startingLoc);
        if (! Location.isWholeFileLoc(startingLoc))
            result += ":" + Location.toOffset(startingLoc);
        result += ": ";
        if (ttype == TagConstants.IDENT)
            result += "IDENT (" + identifierVal.toString() + ")";
        else if (ttype == TagConstants.CHARLIT || ttype == TagConstants.INTLIT
                 || ttype == TagConstants.LONGLIT
                 || ttype == TagConstants.FLOATLIT
                 || ttype == TagConstants.DOUBLELIT
                 || ttype == TagConstants.STRINGLIT)
            result += (PrettyPrint.inst.toString(ttype) + " ("
                       + PrettyPrint.toCanonicalString(ttype, auxVal) + ")");
        else if (ttype == TagConstants.LEXICALPRAGMA
                 || ttype == TagConstants.MODIFIERPRAGMA
                 || ttype == TagConstants.TYPEDECLELEMPRAGMA
                 || ttype == TagConstants.STMTPRAGMA)
            result += PrettyPrint.inst.toString(ttype) + " (" + auxVal.toString() + ")";
        else result += PrettyPrint.inst.toString(ttype);
        return result;
    }


    /** Check the invariants of <code>this</code>. */

    public void zzz() {
        Assert.notFalse(ttype != TagConstants.IDENT
                        || identifierVal != null);
        Assert.notFalse(ttype != TagConstants.INTLIT
                        || auxVal instanceof Integer);
        Assert.notFalse(ttype != TagConstants.LONGLIT
                        || auxVal instanceof Long);
        Assert.notFalse(ttype != TagConstants.FLOATLIT
                        || auxVal instanceof Float);
        Assert.notFalse(ttype != TagConstants.DOUBLELIT
                        || auxVal instanceof Double);
        Assert.notFalse(ttype != TagConstants.STRINGLIT
                        || auxVal instanceof String);
        Assert.notFalse(ttype != TagConstants.CHARLIT
                        || auxVal instanceof Integer);
        Assert.notFalse(ttype != TagConstants.LEXICALPRAGMA
                        || auxVal == null || auxVal instanceof LexicalPragma);
        Assert.notFalse(ttype != TagConstants.MODIFIERPRAGMA
                        || auxVal == null || auxVal instanceof ModifierPragma);
        Assert.notFalse(ttype != TagConstants.STMTPRAGMA
                        || auxVal == null || auxVal instanceof StmtPragma);
        Assert.notFalse(ttype != TagConstants.TYPEDECLELEMPRAGMA
                        || auxVal == null || auxVal instanceof TypeDeclElemPragma);
    }
}
