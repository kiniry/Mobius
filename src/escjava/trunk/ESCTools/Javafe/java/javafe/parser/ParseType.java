/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser;

import javafe.ast.*;
import javafe.util.StackVector;

/**
 * Parses java types.
 * Extended by {@link javafe.ast.ParseExpr}.
 *
 * @see javafe.ast.ASTNode
 * @see javafe.ast.ParseUtil
 * @see javafe.ast.ParseExpr
 */

public class ParseType extends ParseUtil
{
    public ParseType() {
	//@ set seqIdentifier.elementType = \type(Identifier)
	//@ set seqIdentifier.owner = this

	//@ set nameIdLocs.owner = this
	//@ set nameDotLocs.owner = this
    }

    //* Internal working storage for parseName function
    //@ invariant seqIdentifier.elementType == \type(Identifier)
    //@ invariant seqIdentifier.owner == this
    protected final /*@non_null*/ StackVector seqIdentifier
            = new StackVector();



    /** Parse an <TT>Identifier</TT>. */
    //@ requires l.m_in != null
    //@ ensures \result != null
    public Identifier parseIdentifier(/*@non_null*/ Lex l) {
	if( l.ttype != TagConstants.IDENT ) {
            if ( l.ttype == TagConstants.UNKNOWN_KEYWORD)
                fail(l.startingLoc, 
                     "Expected an identifier; Unrecognized keyword");
            else
                fail(l.startingLoc, "Expected an identifier");
	}
	Identifier r = l.identifierVal;
	l.getNextToken();
	return r;
    }

    /* The following private ivars are used in parseName. 
     * They cannot be defined inside parseName because they would be 
     * reallocated at each invocation.
     * They cannot be defined as static variables inside parseName because 
     * then the code would not be thread-safe.
     */
    //@ invariant nameIdLocs.length>=10
    //@ invariant nameIdLocs.owner == this
    private /*@non_null*/ int nameIdLocs[]  = new int[10];
    //@ invariant nameDotLocs.length == nameIdLocs.length
    //@ invariant nameDotLocs.owner == this
    private /*@non_null*/ int nameDotLocs[] = new int[nameIdLocs.length];

    /** Parse a <TT>Name</TT>.
     <PRE>
     Name:
     Identifier ( . Identifier ) *
     </PRE>
     */

    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    public Name parseName(Lex l) {
        if (l.ttype != TagConstants.IDENT) {
            if (l.ttype == TagConstants.UNKNOWN_KEYWORD)
                fail(l.startingLoc,
                     "Expected a Name, got '"+PrettyPrint.inst.toString(l.ttype)+"'" +
                     "; Unrecognized keyword");
            else
                fail(l.startingLoc,
                     "Expected a Name, got '"+PrettyPrint.inst.toString(l.ttype)+"'");
        }
        Identifier id = l.identifierVal;
        int loc = l.startingLoc;
        l.getNextToken();
        if (l.ttype != TagConstants.FIELD || l.lookahead(1) != TagConstants.IDENT)
            return SimpleName.make(id, loc);

        // Deal with less common, multiple-name case...
        seqIdentifier.push();
        seqIdentifier.addElement(id);
        int stkPtr = 0;
        nameIdLocs[stkPtr] = loc;
        /*@ loop_invariant stkPtr<nameIdLocs.length &&
         stkPtr == (seqIdentifier.elementCount
         - seqIdentifier.currentStackBottom)-1 */
        while (l.ttype == TagConstants.FIELD
               && l.lookahead(1) == TagConstants.IDENT) {
            // need to use lookahead for "import Name . *" case
            nameDotLocs[stkPtr++] = l.startingLoc;
            l.getNextToken();  // swallow the FIELD

            if( l.ttype != TagConstants.IDENT ) { 
                if ( l.ttype == TagConstants.UNKNOWN_KEYWORD )
                    fail(l.startingLoc, ("Expected an identifier, got '"
                                         +PrettyPrint.inst.toString(l.ttype)+"'" +
                                         "; Unrecognized keyword"));
                else
                    fail(l.startingLoc, ("Expected an identifier, got '"
                                         +PrettyPrint.inst.toString(l.ttype)+"'"));
            }
            seqIdentifier.addElement( l.identifierVal );

            // Check for resizing
            if( stkPtr == nameIdLocs.length ) {
                // Extend it
                int nuid[] = new int[2*nameIdLocs.length];
                //@ set nuid.owner = this
                System.arraycopy(nameIdLocs, 0, nuid, 0, nameIdLocs.length);
                int nudot[] = new int[2*nameIdLocs.length];
                //@ set nudot.owner = this
                System.arraycopy(nameDotLocs, 0, nudot, 0, nameIdLocs.length-1);
                nameDotLocs = nudot;
                nameIdLocs = nuid;
            }
            nameIdLocs[stkPtr] = l.startingLoc;
            l.getNextToken();
        }
        //@ assume stkPtr>0   // loop always runs at least once

        // Id locations in nameIdLocs[0 .. stkPtr inclusive]
        // Dot locations in nameIdLocs[0 .. stkPtr-1 inclusive]

        // Copy arrays
        int ids[] = new int[stkPtr+1];
        System.arraycopy(nameIdLocs, 0, ids, 0, stkPtr+1);
        int dots[] = new int[stkPtr];
        System.arraycopy(nameDotLocs, 0, dots, 0, stkPtr);
        return CompoundName.make(IdentifierVec.popFromStackVector(seqIdentifier),
                                 ids, dots);
    }

    /** Parse a <TT>TypeName</TT>.
     <PRE>
     TypeName:
     Name [TypeModifierPragmas]
     </PRE>
     */

    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    //@ ensures \result.syntax
    public TypeName parseTypeName(Lex l) {
        Name name = parseName(l);
        TypeModifierPragmaVec modifiers = parseTypeModifierPragmas(l);
        return TypeName.make( modifiers, name );
    }

    /** Parse square bracket pairs.
     Wraps argument <TT>type</TT> in <TT>ArrayType</TT> objects
     accordingly.
     <PRE>
     BracketPairs:
     (LSQBRACKET RSQBRACKET)*
     </PRE>
     <P>Warning: when this method sees "{'[' ']'}* {'[' not-']'}", it
     returns with "l" pointing to the '[' just before the not-']'
     */

    //@ requires l != null && type != null && l.m_in != null
    //@ requires type.syntax
    //@ ensures \result != null
    //@ ensures \result.syntax
    public Type parseBracketPairs(Lex l, Type type) {
        /*
         most of this code is to preserve the warning in comment above.
         also, it is now recursive to put the annotations on the current dimensions.
         */
        if (l.ttype == TagConstants.LSQBRACKET) {
            int loc=l.startingLoc;
            int i = 1;
            boolean done = false;
            while (!done) {
                switch (l.lookahead(i)) {
                    case TagConstants.TYPEMODIFIERPRAGMA:
                        i++;
                        break;
                    case TagConstants.RSQBRACKET:
                        done=true;
                        break;
                    default:
                        return type;
                }
            }
            l.getNextToken();
            TypeModifierPragmaVec modifiers	= parseTypeModifierPragmas(l);
            expect( l, TagConstants.RSQBRACKET );
            type = ArrayType.make( modifiers,
                                   parseBracketPairs(l,type), loc);
        }
        /* old impl:
         while(l.ttype == TagConstants.LSQBRACKET 
         && l.lookahead(1) == TagConstants.RSQBRACKET ) {
         type = ArrayType.make( type, l.startingLoc );
         l.getNextToken();
         expect( l, TagConstants.RSQBRACKET );
         }
         */
        return type;
    }
    
    
    //@ requires l != null && l.m_in != null
    public TypeModifierPragmaVec parseTypeModifierPragmas(/*@non_null*/ Lex l) {
        if (l.ttype != TagConstants.TYPEMODIFIERPRAGMA) return null;
        TypeModifierPragmaVec seq = TypeModifierPragmaVec.make();
        do {
            seq.addElement((TypeModifierPragma)l.auxVal);
            l.getNextToken();
        } while (l.ttype == TagConstants.TYPEMODIFIERPRAGMA);
        return seq;
    }
    
    /**
     * Is a tag a PrimitiveType keyword?
     */
    public boolean isPrimitiveKeywordTag(int tag) {
        switch( tag ) {
            case TagConstants.BOOLEAN:
            case TagConstants.BYTE:
            case TagConstants.SHORT:
            case TagConstants.INT:
            case TagConstants.LONG:
            case TagConstants.CHAR:
            case TagConstants.FLOAT:
            case TagConstants.DOUBLE:
            case TagConstants.VOID:
                return true;

            default:
                return false;
        }
    }


    /** Parses a PrimitiveType. 
     Returns null on failure.
     <PRE>   
     PrimitiveType: one of
     boolean byte short int long char float double void
     </PRE>
     */

    //@ requires l != null && l.m_in != null
    //@ ensures \result != null ==> \result.syntax
    public PrimitiveType parsePrimitiveType(Lex l) {

        int tag;

        switch( l.ttype ) {
            case TagConstants.BOOLEAN: tag = TagConstants.BOOLEANTYPE; break;
            case TagConstants.BYTE:    tag = TagConstants.BYTETYPE;    break;
            case TagConstants.SHORT:   tag = TagConstants.SHORTTYPE;   break;
            case TagConstants.INT:     tag = TagConstants.INTTYPE;     break;
            case TagConstants.LONG:    tag = TagConstants.LONGTYPE;    break;
            case TagConstants.CHAR:    tag = TagConstants.CHARTYPE;    break;
            case TagConstants.FLOAT:   tag = TagConstants.FLOATTYPE;   break;
            case TagConstants.DOUBLE:  tag = TagConstants.DOUBLETYPE;  break;
            case TagConstants.VOID:    tag = TagConstants.VOIDTYPE;    break;
            default: return null;	// Fail!
        }
        // get here => tag is defined
    
        int loc = l.startingLoc;
        l.getNextToken();
        return PrimitiveType.make( tag, loc );
    }
  
    /** Parse a type, either a primitive type, a type name, 
     but not an array type.
     <PRE>
     PrimitiveTypeOrTypeName:
     PrimitiveType
     TypeName
     </PRE>
     */
  
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    //@ ensures \result.syntax
    public Type parsePrimitiveTypeOrTypeName(Lex l) {
        Type type = parsePrimitiveType(l);
        if( type != null ) 
            return type;
        else
            return parseTypeName(l);
    }
  
    /** Parse a <TT>Type</TT>, 
     either a primitive type, a type name, or an array type.
     <PRE>
     Type:
     PrimitiveTypeOrTypeName BracketPairs
     </PRE>
     */
  
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    //@ ensures \result.syntax
    public Type parseType(Lex l) {
        Type type = parsePrimitiveTypeOrTypeName(l);
    
        // Allow for brackets on end 
        return parseBracketPairs(l, type);
    }
  
}
