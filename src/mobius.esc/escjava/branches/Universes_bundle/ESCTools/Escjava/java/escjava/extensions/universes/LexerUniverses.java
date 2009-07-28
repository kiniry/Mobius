/**
 * 
 */
package escjava.extensions.universes;

import javafe.ast.Identifier;
import escjava.extensions.IESCLexerComponentView;

/**
 * This class defines all the functionality related to the
 * lexer of Universe type system.
 * 
 * @author Aleksy Schubert
 *
 */
public class LexerUniverses implements IESCLexerComponentView {

	/** The mark for the first lexer tag */
	private int FIRSTTAG;
	/** The lexer tag for the peer annotation */
    private int PEER;
    /** The lexer tag for the readonly annotation */
    private int READONLY;
    /** The lexer tag for the rep annotation */
    private int REP;
	/** The mark for the last lexer tag */    
	private int LASTTAG;

    /**
     * Array collecting String representations of ESC
     * identifiers.
     */
    private /*@ non_null @*/ String[] stringRep = {
    		"\\peer",
    		"\\readonly",
    		"\\rep"
    };
    
    /**
     * Array collecting Universe type annotations represented
     * as {@link Identifier}s.
     */ 
 	private /*@ non_null @*/ Identifier[] identifiers = new Identifier[0];
	
	/**
	 * Three numbers are reserved for PEER, READONLY, and REP.
	 * Additionally internal {@link Identifier}s cache is
	 * created. <code>RuntimeException</code> is thrown when
	 * this method is called more than once.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#reserveTagConstants(int)
	 */
	public int reserveTagConstants(int firstFree) {
		if (PEER==0) {
			PEER = firstFree;
			FIRSTTAG = firstFree;
			READONLY = firstFree+1;
			REP = firstFree+2;
			LASTTAG = firstFree+2;
			identifiers = new Identifier[3];
		 	identifiers[PEER-FIRSTTAG]=Identifier.intern(stringRep[PEER-FIRSTTAG]);
		    identifiers[READONLY-FIRSTTAG]=Identifier.intern(stringRep[READONLY-FIRSTTAG]);
		    identifiers[REP-FIRSTTAG]=Identifier.intern(stringRep[REP-FIRSTTAG]);
			return firstFree+3;
		} else {
			throw new RuntimeException("Tags already initialized.");
		}
	}

	/**
	 * Universes do not define any new check tags.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#checkFromString(String)
	 */
	public int checkFromString(String s) {
		return -1;
	}

	/**
	 * This method looks up the <code>keyword</code> in the
	 * internal {@link Indentifier}s cache.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#fromIdentifier(Identifier)
	 */
	public int fromIdentifier(Identifier keyword) {
		for (int i=0; i<identifiers.length;i++) {
			if (keyword == identifiers[i]) return i+FIRSTTAG;
		}
		return 0;
	}

	/**
	 * Universes modifiers are ESC keywords so we check if the
	 * given tag is within the range of Universes tags.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#isKeywordTag(int)
	 */
	public boolean isKeywordTag(int tag) {
		return (FIRSTTAG <= tag && tag <= LASTTAG);
	}

	/**
	 * There are no redundant tags in Universes so trivial implementation.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#isRedundant(int)
	 */
	public boolean isRedundant(int tag) {
		return false;
	}

	/**
	 * There are no redundant tags in Universes so trivial implementation.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#makeRedundant(int)
	 */
	public int makeRedundant(int tag) {
		return tag;
	}

	/**
	 * The string is looked up in a local array.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#toString(int)
	 */
	public String toString(int tag) {
		for (int i=0;i<stringRep.length;i++) {
			if (tag==FIRSTTAG+i) return stringRep[FIRSTTAG+i];
		}
		return null;
	}

	/**
	 * There are no VC versions of the tags in Universes.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#toVcString(int)
	 */
	public String toVcString(int tag) {
		return null;
	}

	/**
	 * There are no redundant tags in Universes so trivial implementation.
	 * 
	 * @see escjava.extensions.IESCLexerComponentView#unRedundant(int)
	 */
	public int unRedundant(int tag) {
		return tag;
	}
}
