/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.parser;

import escjava.Main;
import escjava.ast.*;
// This import is necessary to override javafe.ast.TagConstants.
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;

import java.io.IOException;

import javafe.ast.*;
import javafe.SrcTool;
import javafe.parser.Lex;
import javafe.parser.Parse;
import javafe.parser.PragmaParser;
import javafe.parser.Token;
import javafe.util.Assert;
import javafe.util.CorrelatedReader;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;

import java.util.ArrayList;
import java.util.Vector;
/**
 Grammar:

 <pre>
 Pragma ::= LexicalPragma | ModifierPragma | TypeDeclElemPragma | StmtPragma

 LexicalPragma ::= "nowarn" [ Idn [',' Idn]* ] [';']


 StmtPragma ::= SimpleStmtPragma [';']
 | ExprStmtPragma SpecExpr [';']
 | 'set' PrimaryExpr '=' SpecExpr [';']

 SimpleStmtPragma ::= 'unreachable'

 ExprStmtPragma ::= 'assume' | 'assume_redundantly'
 | 'assert' | 'assert_redundantly' 
 | 'loop_inv' | 'loop_invariant' | 'loop_invariant_redundantly'
 | 'decreases' | 'decreases_redundantly'
 | 'loop_predicate' 
 | 'maintaining' | 'maintaining_redundantly'
 | 'decreasing' | 'decreasing_redundantly'

 TypeDeclElemPragma ::=
 ExprDeclPragma SpecExpr [';']
 | 'ghost' Modifiers Type VariableDeclarator [';']
 | 'still_deferred' Idn [',' Idn]* [';']

 ExprDeclPragma ::= 'axiom' | 'invariant' | 'invariant_redundantly'


 ModifierPragma ::=
 [PrivacyPragma] [BehaviorPragma] SimpleModifierPragma 
 [PrivacyPragma] [BehaviorPragma] NonSimpleModifierPragma 

 NonSimpleModifierPragma ::=
 | ['also'] ExprModifierPragma SpecExpr [';']
 | ['also'] VarExprModifierPragma '(' Type Idn ')' SpecExpr [';']
 | ['also'] 'monitored_by' SpecExpr [',' SpecExpr]* [';']
 | ['also'] ModifierPragma SpecDesignator [',' SpecDesignator]* [';']

 PrivacyPragma ::= 'public' | 'private' | 'protected'

 BehaviorPragma ::= 'behavior' | 'normal_behavior' | 'exceptional_behavior'

 SimpleModifierPragma ::= 'uninitialized' | 'monitored' 
 | 'non_null' | 'instance' | 'pure' 
 | 'spec_public' | 'writable_deferred' | 'helper' 
 | 'public' | 'private' | 'protected' 
 | 'spec_protected' | 'model' | 'transient'

 @note kiniry 29 Apr 2003 - the last three above are not yet fully supported

 ExprModifierPragma ::= 'readable_if' | 'writable_if' 
 | 'requires' | 'requires_redundantly' | 'also_requires' (if Main.allowAlsoRequires)
 | 'ensures' | 'ensures_redundantly' | 'also_ensures' 
 | 'pre' | 'pre_redundantly' | 'post' | 'post_redundantly'

 VarExprModifierPragma ::= 'exsures' | 'exsures_redundantly' | 'also_exsures" 
 | 'signals' | 'signals_redundantly'

 ModifierPragma ::= 'modifies' | 'modifies_redundantly' | 'also_modifies' 
 | 'modifiable' | 'modifiable_redundantly'
 | 'assignable' | 'assignable_redundantly'


 DurationClause ::= DurationKeyword '\not_specified' ';'
 | DurationKeyword DurSpecExpr [ 'if' predicate ] ';'

 DurSpecExpr ::= SpecExpr (of type long) OpWithLongResult DurSpecExpr
 | '\duration' '(' MethodInvOrConstructor ')' LongOp DurSpecExpr;

 MethodInvOrConstructorOrNotSpecified ::= MethodInvOrConstructor | '\not_specified';

 InvariantForExpr ::= '\invariant_for' '(' SpecExpr ')' ';'

 SpaceExpr ::= '\space' '(' SpecExpr ')'

 IsInitializedExpr ::= '\is_initialized' '(' Idn ')' ';'

 InvariantFor ::= '\invariant_for' '(' SpecExpr ')' ';'

 WorkingSpaceClause ::= WorkingSpaceKeyword '\not_specified' ';'
 | WorkingSpaceKeyword WorkingSpaceSpecExpr [ 'if' predicate ] ';'

 WorkingSpaceSpecExpr ::= SpecExpr (of type int) OpWithIntResult WorkingSpaceSpecExpr
 | '\working_space' '(' MethodInvOrConstructor ')' IntOp WorkingSpaceSpecExpr

 MethodInvOrConstructor ::= MethodInvocation | ConstructorInvocation

 OpWithIntResult ::= STAR | '/' | '%' | PLUS | '-' | '&' | BITOR | '^'

 WorkingSpaceKeyword ::= 'working_space' | 'working_space_redundantly'

 DurationKeyword ::= 'duration' | 'duration_redundantly'

 PrivateDataKeyword ::= '\private_data'

 NotModifiedExpr ::= '\not_modified' '(' SpecDesignator [',' SpecDesignator]* ')' ';'

 ReachExpr ::= '\reach' '(' SpecExpr [ ',' Idn [ ',' StoreRefExpr ] ] ')' ';'

 FieldsOfExpr ::= '\fields_of' '(' SpecExpr [ ',' Idn [ ',' StoreRefExpr ] ] ')' ';'

 OtherExpr ::= '\other' [ StoreRefNameSuffix ] ';'

 ReachExpr ::= '\reach' '(' SpecExpr [ ',' Idn [ ',' StoreRefExpr ] ] ')' ';'

 StoreRefList ::= StoreRef [ ',' StoreRef ] ...

 StoreRef ::= StoreRefExpr
 | FieldsOfExpr
 | InformalDescription
 | StoreRefKeyword

 StoreRefExpr ::= StoreRefName [ StoreRefNameSuffix ] ...

 StoreRefName ::= Idn | 'super' | 'this'

 StoreRefNameSuffix ::= '.' Idn | '.' 'this' | '[' SpecArrayRefExpr ']'

 SpecArrayRefExpr ::= SpecExpr | SpecExpr '..' SpecExpr | '*'

 StoreRefKeyword ::= '\nothing' | '\everything' | '\not_specified' | '\private_data'


 ConditionalStoreRefList ::= ConditionalStoreRef [ ',' ConditionalStoreRef ] ...

 ConditionalStoreRef ::= StoreRef [ 'if' Predicate ]


 InformalDescription ::= '(*' NonStarClose [ NonStarClose ] ... '*)'

 NonStarClose ::= NonStar | StarsNonClose

 StarsNonClose ::= '*' [ '*' ] ... NonClose

 NonClose ::= any character except ')'

 </pre>

 The grammar of SpecExpr is:

 <pre>
 SpecExpr:
 Name
 | \result
 | \lockset
 | this
 | Literal
 | SpecExpr '.' Idn
 | SpecExpr '[' SpecExpr ']'
 | UnOp SpecExpr
 | '(' Type ')' SpecExpr
 | SpecExpr BinOp SpecExpr
 | SpecExpr 'instanceof' Type
 | Function '(' [ SpecExpr [ ',' SpecExpr ]* ] ')'
 | '\type' '(' Type ')'
 | SpecExpr '?' SpecExpr ':' SpecExpr
 | '(' {'\forall'|'\exists'} Type Idn [',' Idn]* ';' [[SpecExpr] ';'] SpecExpr ')'
 | '(' {'\lblpos'|'\lblneg'} Idn SpecExpr ')'
 | '(' SpecExpr ')'
 | Name '.' this                         [1.1]
 | Name ([])* '.' class                  [1.1]
 | JmlSpecExpr

 JmlSpecExpr ::= '\nothing' | '\everything' | '\not_specified'

 Function ::= '\fresh' | '\nonnullelements' | '\elemtype' | '\max' | '\old'
 | '\typeof' | '\not_modified' | '\nowarn' | '\nowarn_op' | '\warn' | '\warn_op'

 UnOp ::= '+' | '-' | '!' | '~'

 BinOp ::= '+' | '-' | '*' | '/' | '%' | '<<' | '>>' | '>>>'
 | '<' | '<=' | '==' | '!=' | '>=' | '>'
 | '&' | '|' | '^' | '&&' | '||'
 </pre>

 * <p> Also, the grammar for Type is extended (recursively) with the
 * new base type 'TYPE'.
 *
 * <p> Expressions in redundant specifications (e.g.,
 * requires_redundantly ...) are only parsed if
 * <code>Main.checkRedundantSpecs</code> is true.
 *
 * @note 'SC' == Statically Checkable or otherwise useful 'HPT' == Handle at
 * Parse-time 'AAST' == 'Augments Abstract Symbol Tree' Final 0-5 indicates
 * difficulty of implementation; 0 being easiest.  All estimates and
 * implementation/design guesses were made by Joe Kiniry on 29 April 2003.
 *
 * @note kiniry 24 Jan 2003 - All rules named Jml* added by
 * kiniry@cs.kun.nl starting on 24 Jan 2003.
 *
 * @todo kiniry 24 Jan 2003 - Make semicolon at end of 'nowarn' lexical
 * pragma non-optional.  This requires updating spec files &c.
 *
 * @todo kiniry 24 Jan 2003 - Permit 'non_null' annotations on arguments
 * in overrides of methods. Make such specifications redundant.
 *
 * @todo kiniry 31 Jan 2003 - Check semantics of non_null in ESC/Java
 * vs. JML.
 *
 * @todo kiniry 24 Jan 2003 - Permit splitting syntactic constructs
 * across multiple @code{//@@} comments.
 *
 * @todo kiniry 19 May 2003 - Need to add grammar expressions above
 * for constraints.
 *
 * @todo kiniry 9 July 2003 - Support for \not_specified is scattered all over the
 * code right now---perhaps we can refactor and clean up?  It is sometimes parsed
 * and discarded, sometimes recognized and ignored, etc.
 *
 * @see escjava.Main.checkRedundantSpecs
 */

public class EscPragmaParser extends Parse implements PragmaParser
{
    private static final boolean DEBUG = false;
    
    /** 
     * The informal-predicate decoration is associated with a true-valued boolean
     * literal expression, if the concrete syntax of this expression was an informal
     * comment.  The value associated with the decoration is the string of the
     * informal predicate (i.e., the comment itself).
     */
    public static final ASTDecoration informalPredicateDecoration =
        new ASTDecoration("informalPredicate");

    /**
     * The lexer associated with this pragma parser from which we will read tokens.
     */
    private /*@ non_null @*/ EscPragmaLex scanner;

    public int NOTHING_ELSE_TO_PROCESS = -2;
    public int NEXT_TOKEN_STARTS_NEW_PRAGMA = -1;

    /** 
     * The value NOTHING_ELSE_TO_PROCESS means there is nothing else to process.  The
     * value NEXT_TOKEN_STARTS_NEW_PRAGMA means there is something to process and the
     * next thing to read begins a new pragma (or ends the pragma-containing
     * comment).  The other values indicate that the pragma parser is in the middle
     * of parsing some pragma, and is expected to continue this parsing next time it
     * gets control.
     */
    private int inProcessTag;
    /*@ invariant inProcessTag == NOTHING_ELSE_TO_PROCESS || 
     @           inProcessTag == NEXT_TOKEN_STARTS_NEW_PRAGMA ||
     @           inProcessTag == TagConstants.STILL_DEFERRED ||
     @           inProcessTag == TagConstants.MONITORED_BY ||
     @           inProcessTag == TagConstants.MODIFIES ||
     @           inProcessTag == TagConstants.ALSO_MODIFIES ||
     @           inProcessTag == TagConstants.MODIFIABLE ||
     @           inProcessTag == TagConstants.ASSIGNABLE ||
     @           inProcessTag == TagConstants.LOOP_PREDICATE ||
     @           inProcessTag == TagConstants.ALSO; 
     @*/

    private int inProcessLoc;
    private CorrelatedReader pendingJavadocComment;

    /**
     * Maximum # of levels of nesting of annotation comments allowed.  0 == no
     * nesting of annotation comments allowed.
     * 
     * <p> If you change this, change the error message in EscPragmaParser(int) below
     * as well.
     */
    static final int maxAnnotationNestingLevel = 1;

    /**
     * Constructs a new pragma parser with zero nesting level.
     *
     * @see EscPragmaParser(int)
     */
    public EscPragmaParser() {
	this(0);
    }

    /**
     * Constructs a new prama parser at the indicated nesting level.
     *
     * @param level the nesting level of this instance.
     */
    //@ requires level >= 0;
    public EscPragmaParser(int level) {
	PragmaParser pp;
	if (level < maxAnnotationNestingLevel)
	    pp = new EscPragmaParser(level + 1);
	else
	    pp = new ErrorPragmaParser("Annotation comments may be nested "
				       + "at most 1 time");

	scanner = new EscPragmaLex(pp, true);
	scanner.addPunctuation("==>", TagConstants.IMPLIES);
	scanner.addPunctuation("<==", TagConstants.EXPLIES);
	scanner.addPunctuation("<==>", TagConstants.IFF);
	scanner.addPunctuation("<=!=>", TagConstants.NIFF);
	scanner.addPunctuation("<:", TagConstants.SUBTYPE);
	scanner.addPunctuation("..", TagConstants.DOTDOT);
	scanner.addPunctuation("<-", TagConstants.LEFTARROW);
	scanner.addPunctuation("->", TagConstants.RIGHTARROW);
	scanner.addPunctuation("{|", TagConstants.OPENPRAGMA);
	scanner.addPunctuation("|}", TagConstants.CLOSEPRAGMA);
	addOperator(TagConstants.IMPLIES, 76, false);
	addOperator(TagConstants.EXPLIES, 76, true);
	addOperator(TagConstants.IFF, 73, true);
	addOperator(TagConstants.NIFF, 73, true);
	addOperator(TagConstants.SUBTYPE, 140, true);
	addOperator(TagConstants.DOTDOT, 1, true);
	scanner.addKeyword("\\real", TagConstants.REAL);
	scanner.addKeyword("\\bigint", TagConstants.BIGINT);
	scanner.addKeyword("\\result", TagConstants.RES);
	scanner.addKeyword("\\lockset", TagConstants.LS);
	scanner.addKeyword("\\TYPE", TagConstants.TYPETYPE);
	scanner.addKeyword("\\everything",TagConstants.EVERYTHING);
	scanner.addKeyword("\\nothing",TagConstants.NOTHING);
	scanner.addKeyword("\\not_specified",TagConstants.NOT_SPECIFIED);
	scanner.addKeyword("\\such_that",TagConstants.SUCH_THAT);
	inProcessTag = NOTHING_ELSE_TO_PROCESS;
    }

    /**
     * @param tag the comment tag character to check.
     * @return true iff tag is an '@' or an '*' character.
     */
    public boolean checkTag(int tag) {
	if (Main.options().parsePlus && tag == '+') return true;
        return tag == '@' || tag == '*' ;
    }

    /**
     * Restart a pragma parser on a new input stream.  If <code>this</code> is
     * already opened on another {@link CorrelatedReader}, close the old reader.
     *
     * @param in the reader from which to read.
     * @param eolComment a flag that indicates we are parsing an EOL
     * comment (a comment that starts with "//").
     */
    public void restart(/*@ non_null @*/ CorrelatedReader in, 
                        boolean eolComment) {
        try {
            int c = in.read();
            //System.out.println("restart: c = '"+(char)c+"'");

	    if (Main.options().parsePlus && c == '+') {
		c = in.read();
		if (c != '@') {
		    //Not an annotation or doc comment after all - skip to end
		    while (in.read() != -1) {}
		    return;
		}
	    }

            switch (c) {
                case '@':
                    /* Normal escjava annotation: */

                    eatWizardComment(in);
                    in = new JmlCorrelatedReader(in,
					     eolComment ?
					     JmlCorrelatedReader.EOL_COMMENT :
					     JmlCorrelatedReader.C_COMMENT);
                    /*
                     * At this point, <code>in</code> has been
                     * trimmed/replaced as needed to represent the
                     * annotation part of the comment (if any -- it may be
                     * empty).
                     */
                    scanner.restart(in);
                    inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
                    break;

                case '*':
                    if (eolComment) {
                        // This is not a Javadoc comment, so ignore
                        inProcessTag = NOTHING_ELSE_TO_PROCESS;
                    } else {
                        // Javadoc comment -- look for <esc> ... </esc> inside

                        if (pendingJavadocComment != null) {
                            pendingJavadocComment.close();
                        }
                        pendingJavadocComment = in;
                        processJavadocComment();
                    }
                    break;

                default:
                    fail(in.getLocation(),
		      "Bad starting character on comment:"+ c + " " + (char)c);
            }
        } catch (IOException e) {
            ErrorSet.fatal(in.getLocation(), e.toString());
        }
    }

    /**
     * Parse embedded &lt;esc&gr; ... &lt;/esc&gt; in Javadoc comments.
     *
     * @return a flag indicating if an embedded comment was recognized.
     * @exception IOException if something goes wrong during reading.
     */
    private boolean processJavadocComment() throws IOException {
        if (pendingJavadocComment == null) {
            return false;
        }
/*
        final String startEnclosedPragma = "<esc>";
        final String endEnclosedPragma = "</esc>";

	int startLoc = scanFor(pendingJavadocComment, startEnclosedPragma);
*/
	int startLoc = scanForOpeningTag(pendingJavadocComment);
        if (startLoc == Location.NULL) {
            pendingJavadocComment = null;
            inProcessTag = NOTHING_ELSE_TO_PROCESS;
            return false;
        }

        // Mark the current character, the first character inside the enclosed
        // pragma:
        pendingJavadocComment.mark();

        if (scanFor(pendingJavadocComment, endTag) != Location.NULL) {
            // Restrict "pendingJavadocComment" to just before endEnclosedPragma
            CorrelatedReader nu =
                pendingJavadocComment.createReaderFromMark(endTag.length());
            nu = new JmlCorrelatedReader(nu, JmlCorrelatedReader.JAVADOC_COMMENT);
            scanner.restart(nu);
            inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
            return true;
        } else {
            ErrorSet.error(startLoc,
                           "Pragma in javadoc comment is not correctly " +
                           "terminated (missing " + endTag + ")");
            pendingJavadocComment = null;
            inProcessTag = NOTHING_ELSE_TO_PROCESS;
            return false;
        }
    } //@ nowarn Exception // IndexOutOfBoundsException

    /**
     * Eat any wizard inserted comment at the start of an escjava annotation.
     *
     * <p> May side-effect the mark of <code>in</code>.
     *
     * <p> Eats "([^)]*)", if present, from <code>in</code>.
     *
     * @param in the stream from which to read.
     */
    private void eatWizardComment(/*@ non_null @*/ CorrelatedReader in) 
            throws IOException {
        in.mark();
        int cc = in.read();
        if (cc != '(') {
            in.reset();
            return;
        }
	  
        // Handle (...) comment:
        // Skip up to and including the next close paren:
        do {
            cc = in.read();
            if (cc == -1 || cc == '\n') {
                // At end-of-comment or end-of-line but still no close paren:
                ErrorSet.error(in.getLocation(),
                               "Badly formed wizard comment (missing `)')");
                return;
            }
        } while (cc != ')');
    }

    /** 
     * Scans input stream for a string matching the parameter
     * <code>match</code>. Only works if the first character is not repeated in the
     * string.
     *
     * <p> If present, the location of the match is returned.  If not present,
     * <code>Location.NULL</code> is returned.
     *
     * <p> Requires that <code>in</code> is not closed.
     *
     * @param in the stream from which to read.
     * @param match the string to match against the input stream.
     * @return the location of the match, or
     * <code>Location.NULL</code> if there is no match.
     */
    private int scanFor(/*@ non_null @*/ CorrelatedReader in,
			/*@ non_null @*/ String match)
            throws IOException
    {

	int start = match.charAt(0);
	int c = in.read();
	
        mainLoop:
	while(true) {
	    while (c != -1 && c != start )
		c = in.read();

	    if (c == -1) return Location.NULL;
	    int startLoc = in.getLocation();
	    Assert.notFalse(startLoc != Location.NULL);

	    // Have a match for the first character in the string
	    
	    for (int i=1; i<match.length(); i++) {
		c = in.read();
		if (c != match.charAt(i))
		    continue mainLoop;
	    }

	    // Have a match
	    return startLoc;
	}
    }

    private String endTag;
    /**
     * Scans for one of &lt;esc&gt; &lt;jml&gt; &lt;ESC&gt; &lt;JML&gt;.  This is
     * hard-coded to simplify the code.  Also sets the variable endTag to the
     * corresponding tag that closes the opening tag that was found (null if none
     * was found).
     */
    //@ modifies endTag;
    private int scanForOpeningTag(/*@ non_null @*/ CorrelatedReader in)
            throws IOException
    {
	endTag = null;
	
	int start = '<'; // first character of all tags
	int c = in.read();
	while (c != -1) {

	    while (c != -1 && c != start ) c = in.read();

	    if (c == -1) return Location.NULL;
	    int startLoc = in.getLocation();
	    Assert.notFalse(startLoc != Location.NULL);

	    // Have a match for the first character in the string
	    
	    c = in.read();
	    if (c == -1) return Location.NULL;
	    if (c == 'e') {
		c = in.read();
		if (c != 's') continue;
		c = in.read();
		if (c != 'c') continue;
		c = in.read();
		if (c != '>') continue;
		endTag = "</esc>";
	    } else if (c == 'E') {
		c = in.read();
		if (c != 'S') continue;
		c = in.read();
		if (c != 'C') continue;
		c = in.read();
		if (c != '>') continue;
		endTag = "</ESC>";
	    } else if (c == 'j' && Main.options().parsePlus) {
		c = in.read();
		if (c != 'm') continue;
		c = in.read();
		if (c != 'l') continue;
		c = in.read();
		if (c != '>') continue;
		endTag = "</jml>";
	    } else if (c == 'J' && Main.options().parsePlus) {
		c = in.read();
		if (c != 'M') continue;
		c = in.read();
		if (c != 'L') continue;
		c = in.read();
		if (c != '>') continue;
		endTag = "</JML>";
	    } else {
		continue;
	    }
	    // Have a match
	    return startLoc;
	}
	return Location.NULL;
    }

    /**
     * Closes this pragma parser including its scanner and pending Javadoc comment.
     */
    public void close() {
	scanner.close();
	if (pendingJavadocComment != null) {
            pendingJavadocComment.close();
            pendingJavadocComment = null;
	}
    }

    private FieldDecl previousDecl;

    /*
	A bit of refactoring of the old Esc/java design.  This method returns
	a pragma and is called repeatedly to get a series of pragmas until there
	are no more (prior to a non-pragma token).  Sometimes a given
	grammatical context produces more than one pragma.  An example is a
	ghost declaration with more than one identifier.  The previous design
	required the EscPragmaParser object to keep enough context to resume
	the parsing in the middle, via continuePragma().  

	I've improved (I hope) on this by instituting a queue in this object.
	Pragmas are returned from the queue if there are any, until the queue
	is empty.  If the queue is empty, then the regular parsing occurs.
	If the input naturally produces a bunch of pragmas, then all but the
	first is put in the queue, and the first one is returned.  This way
	we can consistently parse either (a) simple keywords, (b) up to a 
	semicolon, or (c) up to the EOF marking the end of the pragma.

	This will simplify the handling of multiple annotations in one pragma
	comment and will simplify the logic overall as well.
			-- DRCok 7/23/2003
    */

    private java.util.LinkedList pragmaQueue = new java.util.LinkedList();
    protected class SavedPragma {
	public int loc;
	public int ttype;
	public Object auxval;
	public SavedPragma(int l, int t, Object o) {
		loc = l;
		ttype = t;
		auxval = o;
	}
    }
    public void savePragma(int l, int t, Object o) {
	pragmaQueue.addLast(new SavedPragma(l,t,o));
    }
    public boolean getPragma(Token dst) {
	if (pragmaQueue.isEmpty()) return false;
	SavedPragma p = (SavedPragma)pragmaQueue.removeFirst();
	dst.startingLoc = p.loc;
	dst.ttype = p.ttype;
	dst.auxVal = p.auxval;
	return true;
    }

	// element type is SavedPragma

    /**
     * Parse the next pragma, putting information about it in the provided token
     * <code>dst</code>, and return a flag indicating if there are further pragmas to
     * be parsed.
     *
     * Note: All worrying about 'also' is now done during the desugaring of specs.
     * JML style of using also is preferred.
     *
     * @param dst the token in which to store information about the current pragma.
     * @return a flag indicating if further pragmas need to be parsed.
     * @see Lex
     */
    public boolean getNextPragma(/*@ non_null @*/ Token dst) {
        try {
	    if (getPragma(dst)) return true;
            if (inProcessTag == NOTHING_ELSE_TO_PROCESS) {
                if (DEBUG)
                    Info.out("getNextPragma: Nothing else to process.");
                return false;
            }

            // See if we need to continue a previous pragma, for example
            // "monitored_by", which can take multiple SpecExprs
            if ((inProcessTag != NEXT_TOKEN_STARTS_NEW_PRAGMA) &&
                (inProcessTag != TagConstants.ALSO)) { 
                continuePragma(dst);
                return true; 
            }

            if (scanner.ttype == TagConstants.EOF) { 
                LexicalPragma PP = scanner.popLexicalPragma();
                if (PP != null) {
                    dst.ttype = TagConstants.LEXICALPRAGMA;
                    dst.auxVal = PP;
                    if (DEBUG)
                        Info.out("getNextPragma: parsed final lexical pragma " + PP +
                                 " at EOF.");
                    return true;
                }

                if (pendingJavadocComment != null) {
                    scanner.close();
                    if (processJavadocComment()) {
                        if (DEBUG)
                            Info.out("getNextPragma: processed javadoc comment at EOF.");
                        return true;
                    }
                }
                close();
                if (DEBUG)
                    Info.out("getNextPragma: hit EOF, so finishing pragma parsing.");
                return false;
            }
            //@ assume scanner.m_in != null;  // TBW: is this right??  --KRML

	    // FIXME - not everything allows modifiers
	    int prefixModifiers = parseModifiers(scanner);

            // Start a new pragma
            int loc = scanner.startingLoc;
            if (Main.options().parsePlus &&
		scanner.ttype == TagConstants.ADD &&
		scanner.lookahead(1) == TagConstants.EOF) {
		return false;
	    }
	    // Pragmas can start with modifiers
	    //if (scanner.ttype != TagConstants.IDENT)
            //    ErrorSet.fatal(loc, "Pragma must start with an identifier");
	    int tag = scanner.ttype;
	    Identifier kw = null;
	    if (tag == TagConstants.IDENT) {
		kw = scanner.identifierVal;
            	tag = TagConstants.fromIdentifier(kw);
	    }
	    if (tag != TagConstants.IMPORT) {
		// Just because the parent class routines expect
		// to start on the IMPORT token
		scanner.getNextToken();
	    }

            boolean semiNotOptional = false;

            if (DEBUG)
                Info.out("next tag is: " + tag);

            switch (tag) {
                case TagConstants.BEHAVIOR:
                case TagConstants.EXCEPTIONAL_BEHAVIOR:
                case TagConstants.NORMAL_BEHAVIOR:
		case TagConstants.EXAMPLE: 
		case TagConstants.NORMAL_EXAMPLE: 
		case TagConstants.EXCEPTIONAL_EXAMPLE:
		case TagConstants.FOR_EXAMPLE: 
		case TagConstants.IMPLIES_THAT:
                case TagConstants.SUBCLASSING_CONTRACT:
                case TagConstants.ALSO: 
                    // SUPPORT COMPLETE (cok/kiniry)
                    // All desugaring of method specifications
                    // is now performed in the desugaring
                    // step in AnnotationHandler.
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal = SimpleModifierPragma.make(tag, loc);
                    break;

                case TagConstants.NOWARN:
                    dst.ttype = TagConstants.LEXICALPRAGMA;
                    seqIdentifier.push();
                    if (scanner.ttype == TagConstants.IDENT)
                        while (true) {
                            seqIdentifier.addElement(parseIdentifier(scanner));
                            if (scanner.ttype != TagConstants.COMMA) break;
                            scanner.getNextToken(); // Discard COMMA
                        }
                    IdentifierVec checks = IdentifierVec.popFromStackVector(seqIdentifier);
                    dst.auxVal = NowarnPragma.make(checks, loc);
                    if (scanner.ttype == TagConstants.SEMICOLON) 
			scanner.getNextToken();
                    if (scanner.ttype != TagConstants.EOF)
                        ErrorSet.fatal(loc, "Syntax error in nowarn pragma");
                    break;

                case TagConstants.MEASURED_BY: // parsed, unclear semantics (cok)
                case TagConstants.MEASURED_BY_REDUNDANTLY: // parsed, unclear semantics (cok)
                case TagConstants.ALSO_MODIFIES:
                case TagConstants.ASSIGNABLE: // SUPPORT COMPLETE (kiniry)
                case TagConstants.ASSIGNABLE_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MODIFIABLE: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MODIFIABLE_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MODIFIES_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MODIFIES: {
		   do {
		    int t = scanner.ttype;
		    Expr e = null;
		    // deal with special case expressions
		    if (t == TagConstants.NOTHING) {
			scanner.getNextToken();
			e = NothingExpr.make(scanner.startingLoc);
		    } else if (t == TagConstants.NOT_SPECIFIED) {
			scanner.getNextToken();
			e = NotSpecifiedExpr.make(scanner.startingLoc);
		    } else if (t == TagConstants.EVERYTHING) {
			scanner.getNextToken();
			e = EverythingExpr.make(scanner.startingLoc);
		    } else {
			// not \nothing, \not_specified, or \everything, so
			// can only be a comma-separated list of
			// SpecDesignators terminated with an optional ';'
			e = parseExpression(scanner);
			// FIXME - should we parse something more restricted
			// than an Expression - grammar says a store-ref
		    }
		    // deal with optional conditional ('if' <predicate>)
		    t = scanner.ttype;
		    Expr cond = null;
		    if (t == TagConstants.IF) {
			scanner.getNextToken();
			cond = parseExpression(scanner);
		    }
		    // A CondExprModifierPragma is used regardless of whether
		    // the modifier is conditional or not.  If the full
		    // expression is not really a conditional expression
		    // (i.e. it has no 'if'), then the condition parameter is
		    // just "null".
		    CondExprModifierPragma pragma = 
			CondExprModifierPragma.make(
				TagConstants.unRedundant(tag),
						    e, loc, cond);
		    if (TagConstants.isRedundant(tag))
			pragma.setRedundant(true);
		    savePragma(loc,TagConstants.MODIFIERPRAGMA, pragma);
		    if (scanner.ttype != TagConstants.COMMA) break;
		    scanner.getNextToken(); // skip comma
		   } while (true);
		    getPragma(dst);
		    semiNotOptional = true;
                    if (DEBUG)
                        Info.out("getNextPragma: parsed a frame axiom: " + 
                                 dst.ztoString());
		    break;
		}

                case TagConstants.STILL_DEFERRED:
                case TagConstants.MONITORED_BY:{
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    if (DEBUG)
                        Info.out("getNextPragma: parsed a frame axiom: " + 
                                 dst.ztoString());
                    return true;
		}

                case TagConstants.DEPENDS:
                case TagConstants.DEPENDS_REDUNDANTLY: {
                    // SC AAST 4 parsed (cok)
                    int tempTag = TagConstants.unRedundant(tag);
                    inProcessLoc = loc;
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    // FIXME - should this be a primary expression
                    // or maybe even a simple name?
                    Expr target = parseExpression(scanner);
                    int locOp = scanner.startingLoc;
		    expect(scanner, TagConstants.LEFTARROW);
		    Vector list = new Vector();
		    while (true) {
			Expr value = parseExpression(scanner);
			list.add(value);
			if (scanner.ttype != TagConstants.COMMA) break;
			scanner.getNextToken();
		    }
                    DependsPragma pragma = 
                        DependsPragma.make(tempTag, target,
                                           ExprVec.make(list), loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
		    semiNotOptional = true;
                    break;
		}

                case TagConstants.UNREACHABLE:
                    dst.ttype = TagConstants.STMTPRAGMA;
                    dst.auxVal = SimpleStmtPragma.make(tag, loc);
                    if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
                    break;
	
                case TagConstants.ASSERT:
                case TagConstants.ASSERT_REDUNDANTLY: { // SUPPORT COMPLETE (kiniry)
                    dst.ttype = TagConstants.STMTPRAGMA;
                    Expr assertion = parseExpression(scanner);
                    Expr label = null;
                    if (scanner.ttype == TagConstants.COLON) {
                        scanner.getNextToken();
                        label = parseExpression(scanner);
                    }
                    ExprStmtPragma pragma = 
                        ExprStmtPragma.make(TagConstants.unRedundant(tag), 
                                            assertion, label, loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.ASSUME:
                case TagConstants.DECREASES:
                case TagConstants.ASSUME_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.DECREASES_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.DECREASING: // SUPPORT COMPLETE (kiniry)
                case TagConstants.DECREASING_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.LOOP_INVARIANT_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MAINTAINING: // SUPPORT COMPLETE (kiniry)
                case TagConstants.MAINTAINING_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.LOOP_INVARIANT: {
                    dst.ttype = TagConstants.STMTPRAGMA;
                    ExprStmtPragma pragma = 
                        ExprStmtPragma.make(TagConstants.unRedundant(tag), 
                                            parseExpression(scanner), null, loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.LOOP_PREDICATE:
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    semiNotOptional = true;
                    if (DEBUG)
                        Info.out("getNextPragma: parsed a loop predicate: " + 
                                 dst.ztoString());
                    return true;	  

                case TagConstants.SET: {
                    dst.ttype = TagConstants.STMTPRAGMA;
                    Expr target = parsePrimaryExpression(scanner);
                    int locOp = scanner.startingLoc;
                    expect(scanner, TagConstants.ASSIGN);
                    Expr value = parseExpression(scanner);
                    dst.auxVal = SetStmtPragma.make(target, locOp, value, loc);
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.REPRESENTS: // SC HPT AAST 4 SUPPORT COMPLETE (cok)
                case TagConstants.REPRESENTS_REDUNDANTLY: // SC HPT AAST 4 (cok)
		    {
                        dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
			// FIXME - the grammar wants a StoreRefExpr here ???
			int locId = scanner.startingLoc;
			Identifier id = parseIdentifier(scanner);
                        Expr target = AmbiguousVariableAccess.make(
					SimpleName.make(id,locId));
			ExprDeclPragma e;
                        int locOp = scanner.startingLoc;
                        if (scanner.ttype == TagConstants.LEFTARROW ||
			    scanner.ttype == TagConstants.ASSIGN) {
			    scanner.getNextToken();
                            Expr value = parseExpression(scanner);
                            e = ExprDeclPragma.make(
				     TagConstants.unRedundant(tag), 
				     BinaryExpr.make(
				       TagConstants.EQ, target, value, locOp), 
				     loc);
                        } else if (scanner.ttype == TagConstants.SUCH_THAT) {
                            expect(scanner, TagConstants.SUCH_THAT);
                            Expr value = parseExpression(scanner);
                            e = ExprDeclPragma.make(
				    TagConstants.unRedundant(tag), value, loc);
                        } else {
			    ErrorSet.error(locOp,
				"Invalid syntax for a represents" +
				" clause.");
			    // Skip this invalid clause
			    eatThroughSemiColon();
			    return getNextPragma(dst);
			}
			e.setRedundant(TagConstants.isRedundant(tag));
			dst.auxVal = e;
                        semiNotOptional = true;
		    }
                    break;

                case TagConstants.CONSTRAINT_REDUNDANTLY: // SC AAST 4
                case TagConstants.CONSTRAINT: {           // SC AAST 4
		    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    ExprDeclPragma pragma = 
                        ExprDeclPragma.make(TagConstants.unRedundant(tag), 
                                            parseExpression(scanner), loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
		    if (scanner.ttype != TagConstants.SEMICOLON) {
			// FIXME - for clause of constraint needs implementing
			eatThroughSemiColon();
			semiNotOptional = false;
		    }
                    break;
                }

                case TagConstants.AXIOM:
                case TagConstants.INVARIANT:
		case TagConstants.INITIALLY: // SC AAST 4 parsed (cok)
                case TagConstants.INVARIANT_REDUNDANTLY: { // SUPPORT COMPLETE (kiniry)
		    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    ExprDeclPragma pragma = 
                        ExprDeclPragma.make(TagConstants.unRedundant(tag), 
                                            parseExpression(scanner), loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
                    break;
                }

		case TagConstants.IMPORT:
                    // SUPPORT COMPLETE (cok)
                    ErrorSet.caution(loc,"An import statement in an annotation " +
                                     "should begin with 'model import'");
                    scanner.lexicalPragmas.addElement( 
			  ImportPragma.make(parseImportDeclaration(scanner),
                                                                        loc));
			// parseImportDeclaration parses the semicolon

                    return getNextPragma(dst);

                case TagConstants.MODEL:
                    // SUPPORT COMPLETE (cok)
		    if (scanner.lookahead(0) == TagConstants.IMPORT) {
			scanner.lexicalPragmas.addElement( 
			      ImportPragma.make(parseImportDeclaration(scanner),
									loc));
			// parseImportDeclaration parses the semicolon

			return getNextPragma(dst);
		    }
		    prefixModifiers |= Modifiers.ACC_MODEL;
		    // fall-through
                case TagConstants.GHOST: {
                    // SUPPORT COMPLETE (cok)
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
	      
		    int modifiers = parseModifiers(scanner,true);
		    if ((modifiers & prefixModifiers) != 0) {
			ErrorSet.warning(loc,
			     TagConstants.toString(tag) +
			     " annotation has a repeated access modifier");
		    }
		    modifiers |= prefixModifiers;
			
                    ModifierPragmaVec modifierPragmas = this.modifierPragmas;
	      
                    int locType = scanner.startingLoc;
                    Type type = parseType(scanner);
	      
                    // make modifierPragmas non-null, so can retroactively extend
                    if (modifierPragmas == null)
                        modifierPragmas = ModifierPragmaVec.make();
	      
		    if (scanner.ttype == TagConstants.LPAREN) {
			// This is a (model) constructor
			if (tag == TagConstants.GHOST) {
			    ErrorSet.error(loc, 
				"A constructor may not be declared ghost");
			    tag = TagConstants.MODEL;
			}
			// Must be a model constructor
			FormalParaDeclVec args;
    			argListInAnnotation = true;
			try {
			args = parseFormalParameterList(scanner);
			} finally {
			argListInAnnotation = false;
			}
			int locThrowsKeyword;
			if (scanner.ttype == TagConstants.THROWS) {
			    locThrowsKeyword = scanner.startingLoc;
			} else {
			    locThrowsKeyword = Location.NULL;
			}
			TypeNameVec raises = parseTypeNames(scanner, TagConstants.THROWS);
			modifierPragmas = parseMoreModifierPragmas(scanner,
						modifierPragmas);
			int locOpenBrace = Location.NULL;
			BlockStmt body = null;
			if (scanner.ttype == TagConstants.SEMICOLON) {
			    scanner.getNextToken(); // eats semicolon
			} else if (scanner.ttype == TagConstants.LBRACE) {
			    locOpenBrace = scanner.startingLoc;
			    body = parseBlock(scanner, false);
                            // FIXME - the above parses with specOnly=true which will not provide the body
			} else {
			    ErrorSet.fatal(scanner.startingLoc,
				"Invalid syntax - expected a " +
				"semicolon or the start of a constructor body, " +
				"encountered " + 
				TagConstants.toString(scanner.ttype));
			}
			// FIXME - need to add the method into the decl elements of the type
			ConstructorDecl md = ConstructorDecl.make(
						modifiers, modifierPragmas,
						null, args,
						raises, body, locOpenBrace,
						loc, locType, locThrowsKeyword);
			dst.auxVal = ModelConstructorDeclPragma.make(md,loc);
			break;
		    }
                    int locId = scanner.startingLoc;
                    Identifier id = parseIdentifier(scanner);
                    Type vartype = parseBracketPairs(scanner, type);
	      
                    VarInit init = null;
                    int locAssignOp = Location.NULL;
		    if (scanner.ttype == TagConstants.LPAREN) {
			// Have the form
			//     modifiers type id (
			// so this is a method declaration
			if (tag == TagConstants.GHOST) {
			    ErrorSet.error(loc, 
				"A method may not be declared ghost");
			    tag = TagConstants.MODEL;
			}
			// Must be a model method
			FormalParaDeclVec args;
    			argListInAnnotation = true;
			try {
			args = parseFormalParameterList(scanner);
			} finally {
			argListInAnnotation = false;
			}

			int locThrowsKeyword;
			if (scanner.ttype == TagConstants.THROWS) {
			    locThrowsKeyword = scanner.startingLoc;
			} else {
			    locThrowsKeyword = Location.NULL;
			}
			TypeNameVec raises = parseTypeNames(scanner, TagConstants.THROWS);

			modifierPragmas = parseMoreModifierPragmas(scanner,
						modifierPragmas);
			int locOpenBrace = Location.NULL;
			BlockStmt body = null;
			if (scanner.ttype == TagConstants.SEMICOLON) {
			    scanner.getNextToken(); // eats semicolon
			} else if (scanner.ttype == TagConstants.LBRACE) {
			    locOpenBrace = scanner.startingLoc;
			    body = parseBlock(scanner, false);
                            // FIXME - the above parses with specOnly=true which will not provide the body
			} else {
			    ErrorSet.fatal(scanner.startingLoc,
				"Invalid syntax - expected a " +
				"semicolon or the start of a method body, " +
				"encountered " + 
				TagConstants.toString(scanner.ttype));
			}
			// FIXME - need to add the method into the decl elements of the type
			MethodDecl md = MethodDecl.make(
						modifiers, modifierPragmas,
						null, args,
						raises, body, locOpenBrace,
						loc, locId, locThrowsKeyword,
						id, type,locType);
			dst.auxVal = ModelMethodDeclPragma.make(md,loc);
		    } else {
			// Have the form
			//     modifiers type id X
		        // where X is not a ( - it is a = or ;
			// so this is a field declaration
			if (scanner.ttype == TagConstants.ASSIGN) {
			    locAssignOp = scanner.startingLoc;
			    scanner.getNextToken();
			    init = parseVariableInitializer(scanner, false);
			}
			if (scanner.ttype == TagConstants.MODIFIERPRAGMA
			    || scanner.ttype == TagConstants.SEMICOLON ) {
			    // if modifier pragma, retroactively add to modifierPragmas
			    // FIXME - is this still valid ???
			    parseMoreModifierPragmas(scanner, modifierPragmas);
			}

			FieldDecl decl
			    = FieldDecl.make(modifiers, modifierPragmas, 
					     id, vartype, locId, init, locAssignOp );
		  
		  
			if (tag == TagConstants.GHOST) {
			    dst.auxVal = GhostDeclPragma.make(decl, loc);
			} else if (tag == TagConstants.MODEL) {
			    dst.auxVal = ModelDeclPragma.make(decl, loc);
			}
			while (scanner.ttype == TagConstants.COMMA) {
			    scanner.getNextToken(); // skip comma
			    locId = scanner.startingLoc;
			    id = parseIdentifier(scanner);
			    // No bracket pairs allowed with subsequent ids
		 
			    init = null;
			    locAssignOp = Location.NULL;
			    if (scanner.ttype == TagConstants.ASSIGN) {
				locAssignOp = scanner.startingLoc;
				scanner.getNextToken();
				init = parseVariableInitializer(scanner, false);
			    }
			    decl = FieldDecl.make(
				modifiers, modifierPragmas,
				id, type, locId, init, locAssignOp);
			    Object pragma = null;
			    if (tag == TagConstants.GHOST) {
				pragma = GhostDeclPragma.make(decl, locId);
			    } else if (tag == TagConstants.MODEL) {
				pragma = ModelDeclPragma.make(decl, locId);
			    }
			    savePragma( loc, TagConstants.TYPEDECLELEMPRAGMA,
					pragma);

			}
			inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
			semiNotOptional = true;
			if (scanner.ttype == TagConstants.IDENT &&
			    scanner.identifierVal.toString().equals("initially")) {
			    // This usage of 'initially' is deprecated
			    // To get rid of it, just eliminate this if block.
			    // FIXME
                            semiNotOptional = false;
			}
		    }
                    break;
                }

                case TagConstants.SKOLEM_CONSTANT: {
                    dst.ttype = TagConstants.STMTPRAGMA;
	      
                    int locType = scanner.startingLoc;
                    Type type = parseType(scanner);
	      
                    LocalVarDeclVec v = LocalVarDeclVec.make();
                    int nextTtype;
                    
		    loop: while (true) {
                        int locId     = scanner.startingLoc;
                        Identifier id = parseIdentifier(scanner);
                        Type vartype = parseBracketPairs(scanner, type);
		  
                        LocalVarDecl decl
                            = LocalVarDecl.make(Modifiers.NONE, null, id, 
                                                vartype, locId, null, Location.NULL);
                        v.addElement(decl);
		  
                        switch (scanner.ttype) {
                            case TagConstants.COMMA:
                                scanner.getNextToken();
                                continue loop;

                            default:
                                fail( scanner.startingLoc, 
                                      "Expected comma or semicolon in skolem_constant decl");

                            case TagConstants.SEMICOLON:
                                break loop;

                        }
                    }

                    dst.auxVal = SkolemConstantPragma.make(v, locType, 
					scanner.startingLoc);
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.PURE: // SC parsed and checked SUPPORT COMPLETE (cok)

                case TagConstants.HELPER:

		case TagConstants.OPENPRAGMA: // complete (ok)
		case TagConstants.CLOSEPRAGMA: // complete (cok)

                case TagConstants.SPEC_PROTECTED: // SC HPT AAST 3, SUPPORT COMPLETE (cok)
                case TagConstants.SPEC_PUBLIC: // incomplete

                case TagConstants.INSTANCE: // SC AAST 3 parses but no semantics (cok)
                case TagConstants.MONITORED: // incomplete
                case TagConstants.NON_NULL: // incomplete
                case TagConstants.UNINITIALIZED: // incomplete
                case TagConstants.WRITABLE_DEFERRED: // incomplete
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal = SimpleModifierPragma.make(tag, loc);
                    break;

                case TagConstants.ALSO_ENSURES:
                case TagConstants.ALSO_REQUIRES:
                case TagConstants.ENSURES:
		case TagConstants.DIVERGES: // parsed (cok)
		case TagConstants.DIVERGES_REDUNDANTLY: // parsed (cok)
                case TagConstants.ENSURES_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.POSTCONDITION: // SUPPORT COMPLETE (kiniry)
                case TagConstants.POSTCONDITION_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.PRECONDITION: // SUPPORT COMPLETE (kiniry)
                case TagConstants.PRECONDITION_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.REQUIRES_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.WHEN: // NOT SC, parsed but concurrent only (cok)
                case TagConstants.WHEN_REDUNDANTLY: // ditto
                case TagConstants.READABLE_IF:
                case TagConstants.REQUIRES:
                case TagConstants.WRITABLE_IF: {
                    // Note which tages cannot be statically checked.
                    if (tag == TagConstants.WHEN || 
                        tag == TagConstants.WHEN_REDUNDANTLY)
                        noteUnsupportedUncheckableJmlPragma(loc, tag);
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
		    ExprModifierPragma pragma;
		    if (scanner.ttype == TagConstants.NOT_SPECIFIED) {
			pragma =
			    ExprModifierPragma.make(TagConstants.unRedundant(tag), 
				NotSpecifiedExpr.make(scanner.startingLoc), loc);
			scanner.getNextToken();
		    } else {
			// SpecExpr [';']
			pragma =
			    ExprModifierPragma.make(TagConstants.unRedundant(tag), 
						    parseExpression(scanner), loc);
		    }
		    if (TagConstants.isRedundant(tag))
			pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.DURATION:                 // SC HPT 2
                case TagConstants.DURATION_REDUNDANTLY:     // SC HPT 2
                case TagConstants.WORKING_SPACE:            // SC HPT 2
                case TagConstants.WORKING_SPACE_REDUNDANTLY:// SC HPT 2
                    // parsed and returned (cok)
		  {
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
		    CondExprModifierPragma pragma;
		    if (scanner.ttype == TagConstants.NOT_SPECIFIED) {
			// \not_specified ;
			pragma =
			   CondExprModifierPragma.make(TagConstants.unRedundant(tag), 
				NotSpecifiedExpr.make(scanner.startingLoc),loc,null);
			scanner.getNextToken(); // reads semicolon
		    } else {
			// SpecExpr [';']
			pragma =
			   CondExprModifierPragma.make(TagConstants.unRedundant(tag), 
					    parseExpression(scanner),loc, null);
		    }
		    if (TagConstants.isRedundant(tag))
			pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
		    if (scanner.ttype == TagConstants.IF) {
			scanner.getNextToken(); // read the if
			pragma.cond = parseExpression(scanner);
		    }
                    break;
                }

                case TagConstants.ALSO_EXSURES:
                case TagConstants.EXSURES:
                case TagConstants.EXSURES_REDUNDANTLY: // SUPPORT COMPLETE (kiniry)
                case TagConstants.SIGNALS: // SUPPORT COMPLETE (kiniry)
                case TagConstants.SIGNALS_REDUNDANTLY: {
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    expect(scanner, TagConstants.LPAREN);
                    FormalParaDecl arg = parseExsuresFormalParaDecl(scanner);
                    expect(scanner, TagConstants.RPAREN);
                    Expr expr = null;
		    if (scanner.ttype == TagConstants.SEMICOLON)
			expr = LiteralExpr.make(TagConstants.BOOLEANLIT,
                                                Boolean.TRUE,scanner.startingLoc);
		    else
			expr = parseExpression(scanner);
                    VarExprModifierPragma pragma =
                        VarExprModifierPragma.make(TagConstants.unRedundant(tag), 
                                                   arg, expr, loc);
                    if (TagConstants.isRedundant(tag))
                        pragma.setRedundant(true);
                    dst.auxVal = pragma;
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.REFINE:
		{
		    int sloc = scanner.startingLoc;
		    Expr e = parsePrimaryExpression(scanner);
		    if (!(e instanceof LiteralExpr) || 
                            e.getTag() != TagConstants.STRINGLIT) {
			ErrorSet.error(sloc,
				"Expected a string literal after 'refine'");
			eatThroughSemiColon();
		    } else {
			expect(scanner,TagConstants.SEMICOLON);
			scanner.lexicalPragmas.addElement( 
			  RefinePragma.make( (String)((LiteralExpr)e).value, loc));
		    }
                    return getNextPragma(dst);
		}

                // Unsupported JML clauses/keywords.

                // The following clauses must be followed by a semi-colon.
		case TagConstants.IN:
		case TagConstants.IN_REDUNDANTLY:
		case TagConstants.MAPS:
		    // Ignored for now

                case TagConstants.ACCESSIBLE_REDUNDANTLY:
                    // SC HPT AAST 2 unclear syntax and semantics (kiniry)
                case TagConstants.ACCESSIBLE:
                    // SC HPT AAST 2 unclear syntax and semantics (kiniry)
                case TagConstants.BREAKS_REDUNDANTLY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.BREAKS:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.CALLABLE_REDUNDANTLY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.CALLABLE:
                    // unclear semantics (kiniry)
                case TagConstants.CONTINUES_REDUNDANTLY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.CONTINUES:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.NO_WACK_FORALL:
                    // unclear syntax and semantics - note that this is the keyword
                    // 'forall', *NOT* '\forall'
                case TagConstants.HENCE_BY_REDUNDANTLY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.HENCE_BY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.OLD:
                    // unclear semantics (kiniry)
                case TagConstants.RETURNS_REDUNDANTLY:
                    // unclear syntax and semantics (kiniry)
                case TagConstants.RETURNS:
                    // unclear syntax and semantics (kiniry)
                    eatThroughSemiColon();
                    noteUnsupportedCheckableJmlPragma(loc, tag);
                    return getNextPragma(dst);

                // The following clauses are block oriented, thus everything
                // after them up to the next new block must be skipped.
                case TagConstants.ABRUPT_BEHAVIOR:
                    // unclear syntax and semantics (kiniry)
                    ErrorSet.fatal(loc, 
                                   "Encountered a keyword we recognize, " + 
                                   "but do not know how to handle: " +
                                   tag + " " + TagConstants.toString(tag));
                    break;

                // The following clauses are isolated keywords and can be skipped
                // trivially.
                case TagConstants.WEAKLY:
                    // unclear syntax and semantics (kiniry)
                    noteUnsupportedCheckableJmlPragma(loc, tag);
                    return getNextPragma(dst);

                case TagConstants.MODEL_PROGRAM: {
                    // unclear syntax and semantics (cok/kiniry)
		    // SKIP the compound statement
		    expect(scanner,TagConstants.LBRACE);
		    int braceCount = 1;
		    while(true) {
			if (scanner.ttype == TagConstants.LBRACE) {
			    ++braceCount;
			} else if (scanner.ttype == TagConstants.RBRACE) {
			    --braceCount;
			    if (braceCount == 0) {
				scanner.getNextToken();
				break;
			    }
			}
			scanner.getNextToken();
		    }
			// FIXME - parse the compound statement and add it to
			// the pragma
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
		    dst.auxVal = ModelProgamModifierPragma.make(tag,loc);
		    inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
		    // NO SEMICOLON
		    break;
	        }


                // The following clauses have an unknown syntax, so if they are
                // seen then the ESC/Java parser will fail.
                case TagConstants.CHOOSE_IF:
                    // unclear semantics (kiniry)
                case TagConstants.CHOOSE:
                    // unclear semantics (kiniry)
                case TagConstants.INITIALIZER:
                    // SC AAST 4 unclear syntax and semantics (kiniry)
                case TagConstants.OR:
                    // unclear semantics (kiniry)
                case TagConstants.STATIC_INITIALIZER:
                    // SC AAST 4, unclear syntax and semantics (kiniry)
                    ErrorSet.fatal(loc, 
                                   "Encountered a keyword we recognize, " + 
                                   "but do not know how to parse: " +
                                   tag + " " + TagConstants.toString(tag));
                    break;
	
                default:
                    ErrorSet.error(loc, "Unrecognized pragma: " + tag + " " +
                                   TagConstants.toString(tag));
		    // Skip to end
		    while (scanner.ttype != TagConstants.EOF) scanner.getNextToken();
		    return false;
            }

            if (semiNotOptional) {
                eatSemiColon(kw);
                inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
	    }
            if (DEBUG)
                Info.out("getNextPragma: parsed : " + dst.ztoString());
            return true;
        } catch (IOException e) { 
            return false; 
        }
    }

    /**
     * Emit an error message to the user that support for the supplied
     * tag at the specified location is underway by a particular
     * developer.
     */
    private void notePragmaUnderway(int loc, int tag, String username) {
        ErrorSet.fatal(loc, "Unsupported pragma: " + 
                       TagConstants.toString(tag) +
                       "; " + username + "@users.sf.net is working on it.");
    }
    
    /**
     * Emit a caution to the user if verbosity is enabled that the
     * supplied tag at the specified location is unsupported by the
     * current version of ESC/Java but is statically checkable.
     */
    private void noteUnsupportedCheckableJmlPragma(int loc, int tag) {
        if (Info.on)
            ErrorSet.caution(loc, "Unsupported pragma '" + 
		     TagConstants.toString(tag) +
		     "'; ESC/Java will not statically check this spec.");
    }

    /**
     * Emit a caution to the user if verbosity is enabled that the
     * supplied tag at the specified location is unsupported by the
     * current version of ESC/Java and is statically uncheckable.
     */
    private void noteUnsupportedUncheckableJmlPragma(int loc, int tag) {
        if (Info.on)
            ErrorSet.caution(loc, "Unsupported uncheckable pragma '" + 
                             TagConstants.toString(tag) +
                             "' ignored.");
    }

    /**
     * Eat tokens up through and including terminating semi-colon.
     * This method is used to pretend like we are parsing
     * semi-colon-terminated expressions in pragmas that we do not yet
     * really parse or handle.
     *
     * @return the full expression, not including the semi-colon, as a string.
     */
    private String eatThroughSemiColon() {
        StringBuffer sb = new StringBuffer();
        while (scanner.ttype != TagConstants.SEMICOLON) {
            sb.append(TagConstants.toString(scanner.ttype));
            Info.out("eating " + TagConstants.toString(scanner.ttype));
            sb.append(" ");
            scanner.getNextToken();
        }
        // throw away final semi-colon
        scanner.getNextToken();
        return sb.toString();
    }

    /**
     * Eat the next token if it is a semi-colon and, if the next
     * token is a pragma (not EOF, thus not the end of the pragma)
     * then issue an error message indicating that the specified
     * identifier must be semi-colon terminated if it is followed by
     * more pragmas.
     */
    private void eatSemiColon(Identifier kw) {
        if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
        else if (scanner.ttype != TagConstants.EOF)
            ErrorSet.fatal(scanner.startingLoc, 
		   "Semicolon required when a " + kw.toString()
		    + " pragma is followed by another pragma (found "
		    + TagConstants.toString(scanner.ttype) + " instead).");
    }

    /*@ requires inProcessTag == TagConstants.ALSO_MODIFIES ||
      @          inProcessTag == TagConstants.ASSIGNABLE ||
      @          inProcessTag == TagConstants.ASSIGNABLE_REDUNDANTLY ||
      @          inProcessTag == TagConstants.MODIFIABLE ||
      @          inProcessTag == TagConstants.MODIFIABLE_REDUNDANTLY ||
      @          inProcessTag == TagConstants.MODIFIES_REDUNDANTLY ||
      @          inProcessTag == TagConstants.LOOP_PREDICATE ||
      @          inProcessTag == TagConstants.MODIFIES ||
      @          inProcessTag == TagConstants.MONITORED_BY ||
      @          inProcessTag == TagConstants.STILL_DEFERRED;
      @*/
    //@ requires scanner.startingLoc != Location.NULL;
    //@ requires scanner.m_in != null;
    private void continuePragma(/*@ non_null @*/ Token dst) throws IOException {
        if (inProcessTag == TagConstants.STILL_DEFERRED) {
            int locId = scanner.startingLoc;
            Identifier idn = parseIdentifier(scanner);
            dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
            dst.auxVal = StillDeferredDeclPragma.make(idn, inProcessLoc, locId);
        } else if (inProcessTag == TagConstants.MONITORED_BY) {
            dst.startingLoc = inProcessLoc;
	    int tempInProcessTag = inProcessTag;
	    int t = scanner.lookahead(0);
            // deal with special case expressions
	    if (t == TagConstants.NOTHING) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
                                                     NothingExpr.make(scanner.startingLoc), inProcessLoc);
	    } else if (t == TagConstants.NOT_SPECIFIED) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
                                                     NotSpecifiedExpr.make(scanner.startingLoc), inProcessLoc);
	    } else if (t == TagConstants.EVERYTHING) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
                                                     EverythingExpr.make(scanner.startingLoc), inProcessLoc);
	    } else {
	        Expr e = parseExpression(scanner);
                dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
                                                     e, inProcessLoc);
            }
            dst.ttype = TagConstants.MODIFIERPRAGMA;
        } else if (inProcessTag == TagConstants.LOOP_PREDICATE) {
            dst.startingLoc = inProcessLoc;
            Expr e = parseExpression(scanner);
            dst.auxVal = ExprStmtPragma.make(inProcessTag, e, null, inProcessLoc);
            dst.ttype = TagConstants.STMTPRAGMA;
//        } else if (inProcessTag == TagConstants.DEPENDS) {
            // FIXME - not sure why we end up here or what we are supposed to do
        } else {
            System.out.println("UNSUPPORTED TAG " + TagConstants.toString(inProcessTag));
            Assert.precondition(false);
	}

        switch (scanner.ttype) {
            case TagConstants.SEMICOLON:
                scanner.getNextToken();
            case TagConstants.EOF:
                inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
                break;

            case TagConstants.COMMA:
                scanner.getNextToken();
                break;

            default:
                ErrorSet.fatal(scanner.startingLoc,
                               "Unexpected token '" + 
                               TagConstants.toString(scanner.ttype)
                               + "', expected ',', ';' or end-of-file");
        }
    }


    // Special parsing methods for handling quantified expressions.

    /**
     * Parse a "primary expression" from <code>l</code>.  A primary
     * expression is an expression of the form:
     * <pre>
     * \result
     * \lockset
     * (*...*)
     * Function '('
     * '\type' '('
     * '(' {'\forall'|'\exists'} Type
     * '(' {'\lblpos'|'\lblneg'} Idn
     * </pre>
     * or is a "normal" primary expression parsed with
     * <code>ParseExpr.parsePrimaryExpression()</code>.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed expression.
     * @see javafe.parser.ParseExpr#parsePrimaryExpression(javafe.ast.Lex)
     */
    protected Expr parsePrimaryExpression(Lex l) {
        /* Lookahead for:
         *  \result
         *  \lockset
         *  (*...*)
         *  Function '('
         * '\type' '('
         * '(' {'\forall'|'\exists'} Type
         * '(' {'\lblpos'|'\lblneg'} Idn
         */

        Expr primary = null /*@ uninitialized @*/;

        // First parse PrimaryCore into variable primary
        switch(l.ttype) {

            case TagConstants.NOT_SPECIFIED:
                primary = NotSpecifiedExpr.make(l.startingLoc);
                l.getNextToken();
                break;
                
            case TagConstants.EVERYTHING:
                primary = EverythingExpr.make(l.startingLoc);
                l.getNextToken();
                break;
                    
            case TagConstants.NOTHING:
                primary = NothingExpr.make(l.startingLoc);
                l.getNextToken();
                break;
                
            case TagConstants.RES: 
                primary = ResExpr.make(l.startingLoc);
                l.getNextToken();
                break;

            case TagConstants.LS: 
                primary = LockSetExpr.make(l.startingLoc);
                l.getNextToken();
                break;

            case TagConstants.INFORMALPRED_TOKEN:
                primary = LiteralExpr.make(TagConstants.BOOLEANLIT,
                                           new Boolean(true), l.startingLoc);
                informalPredicateDecoration.set(primary, l.auxVal);
                l.getNextToken();
                break;

            case TagConstants.IDENT: 
                { 
                    // First comes a Name...
                    int loc = l.startingLoc;
                    Name n = parseName(l);
                    
                    // May be followed by ( ArgumentListopt ) :
                    if (l.ttype == TagConstants.LPAREN) {
                        int locOpenParen = l.startingLoc;
                        
                        Identifier kw = n.identifierAt(0);
                        int tag = TagConstants.fromIdentifier(kw);
                        
                        if (n.size() != 1) {
			    ExprVec args = parseArgumentList(l);
			    primary = AmbiguousMethodInvocation.make(n, 
                                                                     null, locOpenParen, args);
                            // fail(loc, "Annotations may not contain method calls");
			} else {
                            switch (tag) {
                                case TagConstants.TYPE: {
				    l.getNextToken();
                                    Type subexpr = parseType(l);
                                    primary = TypeExpr.make(loc, l.startingLoc, subexpr);
                                    expect(l, TagConstants.RPAREN);
                                    break;
                                }
                                    
                                case TagConstants.DTTFSA: {
				    l.getNextToken();
                                    Type t = parseType(l);
                                    TypeExpr te = TypeExpr.make(loc, l.startingLoc, t);
                                    expect(l, TagConstants.COMMA);
                                    ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                    args.insertElementAt(te, 0);
                                    primary = NaryExpr.make(loc, l.startingLoc, tag, null, args);
                                    break;
                                }

				case TagConstants.NOT_MODIFIED: {
                                    // SC AAST 4, parsed (cok/kiniry)
				    l.getNextToken();
                                    Expr arg = parseExpression(l);
				    ExprVec args = ExprVec.make(2);
				    ExprVec args2 = ExprVec.make(1);
				    args.addElement(arg);
				    args2.addElement((Expr)arg.clone());
                                    Expr oldex = 
					NaryExpr.make(loc, l.startingLoc, 
					    TagConstants.PRE, null, args2);
				
				    args.addElement(oldex);
                                    primary = NaryExpr.make(loc, l.startingLoc,
					TagConstants.EQ, null, args);
				    primary = BinaryExpr.make(
					TagConstants.EQ, arg, oldex, loc);
				    expect(l,TagConstants.RPAREN);
                                    break;
                                }

				case TagConstants.WACK_NOWARN:
				case TagConstants.NOWARN_OP:
				case TagConstants.WARN:
				case TagConstants.WARN_OP:
                                case TagConstants.FRESH: 
                                case TagConstants.ELEMSNONNULL:
                                case TagConstants.ELEMTYPE:
                                case TagConstants.MAX: 
                                case TagConstants.PRE: // \\old
                                case TagConstants.TYPEOF: {
				    l.getNextToken();
                                    ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                    primary = NaryExpr.make(loc, l.startingLoc, tag, null, args);
                                    break;
                                }

				case TagConstants.WACK_DURATION:
				case TagConstants.WACK_WORKING_SPACE:
				case TagConstants.SPACE:
				{
				    l.getNextToken();
                                    ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                    primary = NaryExpr.make(loc, l.startingLoc, tag, null, args);
                                    break;

				}
                                    
                                default:
                                    // parseArgumentList requires that the scanner (l) must
                                    // be at the LPAREN, so we can't read the LPAREN token
                                    ExprVec args = parseArgumentList(l);
                                    primary = AmbiguousMethodInvocation.make(n, null, locOpenParen, args);
                            }
                        }
                        break;
                    }
                    
                    // Look for 'TypeName . this'
                    if (l.lookahead(0) == TagConstants.FIELD &&
                        l.lookahead(1) == TagConstants.THIS) {
                        expect(l, TagConstants.FIELD);
                        int locThis = l.startingLoc;
                        expect(l, TagConstants.THIS);
                        primary = ThisExpr.make(TypeName.make(n), locThis);
                        break;
                    }

                    // Or ([])* . class:
                    // (need to look ahead fully because of "<type>[] x;" declarations)
                    int i = 0;
                    while ((l.lookahead(i) == TagConstants.LSQBRACKET) &&
                           (l.lookahead(i+1) == TagConstants.RSQBRACKET))
                        i += 2;
                    if ((l.lookahead(i) == TagConstants.FIELD) &&
                        (l.lookahead(i+1) == TagConstants.CLASS)) {
                        Type t = TypeName.make(n);
                        t = parseBracketPairs(l, t);
                        primary = parseClassLiteralSuffix(l, t);
                        break;
                    }

                    // Ok, it must have just been a naked Name:
                    primary = AmbiguousVariableAccess.make(n);
                    break;
                }
      
            case TagConstants.LPAREN: 
                { 
                    // LPAREN Expression RPAREN
                    int locOpenParen = l.startingLoc;
                    l.getNextToken();
                    boolean regularParenExpr = true;
	
                    // First see if we have a (LBLxxx ...) or (quantifier ...)
                    if (l.ttype == TagConstants.IDENT) {
                        Identifier kw = l.identifierVal;
                        int tag = TagConstants.fromIdentifier(kw);
			// If \max is followed by a ( then it is a function,
			// otherwise it is a quantifier and we change the tag.
			if (tag == TagConstants.MAX &&
				l.lookahead(1) != TagConstants.LPAREN)
					tag = TagConstants.MAXQUANT;
                        if ((tag == TagConstants.LBLPOS || tag == TagConstants.LBLNEG) &&
                            l.lookahead(1) == TagConstants.IDENT) {
                            regularParenExpr = false;
                            boolean pos = (tag == TagConstants.LBLPOS);
                            l.getNextToken(); // Discard LBLxxx
                            Identifier label = l.identifierVal;
                            l.getNextToken();
                            Expr e = parseExpression(l);
                            primary = LabelExpr.make(locOpenParen, l.startingLoc,
                                                     pos, label, e);
                            expect(l, TagConstants.RPAREN);
                        } else if (tag == TagConstants.FORALL || 
				   tag == TagConstants.MIN ||
				   tag == TagConstants.MAXQUANT ||
				   tag == TagConstants.NUM_OF ||
				   tag == TagConstants.SUM ||
				   tag == TagConstants.PRODUCT ||
                                   tag == TagConstants.EXISTS) {
                            int lookahead = l.lookahead(1);
                            if (lookahead == TagConstants.IDENT ||
                                isPrimitiveKeywordTag(lookahead)) {
                                regularParenExpr = false;
                                l.getNextToken(); // Discard quantifier
                                Type type = parseType(l);
                                primary = parseQuantifierRemainder(l, tag, 
                                                                   type, locOpenParen);
                            }
                        }
                    }
                    if (regularParenExpr) {
                        Expr e = parseExpression(l);
                        int locCloseParen = l.startingLoc;
                        expect(l, TagConstants.RPAREN);
                        primary = ParenExpr.make(e, locOpenParen, locCloseParen);
                    }
                    break;
                }

            default:
                primary = super.parsePrimaryExpression(l);
        }

        // Ok, parsed a PrimaryCore expression into primary. 
        // Now handle PrimarySuffix*

        return parsePrimarySuffix(l, primary);
    }

    /**
     * Parse the suffix of a "primary expression" from <code>l</code>,
     * given the prefix primary expression <code>primary</code>.
     *
     * @param l the lexer from which to read and parse.
     * @param primary the primary expression previously parsed.
     * @return the parsed expression.
     */
    protected Expr parsePrimarySuffix(Lex l, Expr primary) {
        while(true) {
            primary = super.parsePrimarySuffix(l, primary);

            if ((l.ttype == TagConstants.LSQBRACKET) &&
                (l.lookahead(1) == TagConstants.STAR) &&
                (l.lookahead(2) == TagConstants.RSQBRACKET)) {
                int locOpen = l.startingLoc;
                l.getNextToken();
                l.getNextToken();
                int locClose = l.startingLoc;
                l.getNextToken();
                primary = WildRefExpr.make(primary, locOpen, locClose);
                // and go around again
            } else {
                // no PrimarySuffix left, all done
                return primary;
            }
        }
    }

    /**
     * Parse the balance (everything after the quantifier to the end
     * of the current quantified scope) of a quantifier expression
     * from <code>l</code>.
     *
     * @param l the lexer from which to read and parse.
     * @param tag identifies which kind of quantifier we are parsing.
     * @param type the type of the quantified variable.
     * @param loc the starting location of the quantified expression.
     * @return the parsed quantified expression.
     */
    //@ requires l.m_in != null;
    //@ requires type.syntax;
    /*@ requires tag == TagConstants.FORALL || tag == TagConstants.EXISTS ||
      @          tag == TagConstants.MAX || tag == TagConstants.MIN ||
      @          tag == TagConstants.PRODUCT || tag == TagConstants.SUM ||
      @          tag == TagConstants.NUM_OF;
      @*/
    private /*@ non_null */ GCExpr parseQuantifierRemainder(/*@ non_null @*/ Lex l,
                                                            int tag,
                                                            /*@ non_null @*/ Type type,
                                                            int loc) {
        int idLoc = l.startingLoc;
        Identifier idn = parseIdentifier(l);
        LocalVarDecl v = LocalVarDecl.make(0, null, idn, type, idLoc,
                                           null, Location.NULL);

        GenericVarDeclVec vs = GenericVarDeclVec.make();
        vs.addElement(v);
    
	while (l.ttype == TagConstants.COMMA) {
	    l.getNextToken(); // skip comma
	    idLoc = l.startingLoc;
	    idn = parseIdentifier(l);
	    v = LocalVarDecl.make(0, null, idn, type, idLoc,
                                           null, Location.NULL);
	    vs.addElement(v);
        }

	int locSemi = Location.NULL;
        int endLoc = 0 /*@ uninitialized @*/;
	Expr rangeExpr = null;
        Expr rest = null /*@ uninitialized @*/;

	if (l.ttype == TagConstants.SEMICOLON) {
            l.getNextToken();
	    locSemi = l.startingLoc;
            boolean emptyRange = false;
            if (l.ttype == TagConstants.SEMICOLON) {
                l.getNextToken();  // eat the semicolon
                emptyRange = true;
            }
            rest = parseExpression(l);
            if (!emptyRange && l.ttype == TagConstants.SEMICOLON) {
                // there is a nonempty range expression
                locSemi = l.startingLoc;
                l.getNextToken();  // eat the semicolon
		rangeExpr = rest;
                rest = parseExpression(l);
            }
            endLoc = l.startingLoc;
            expect(l, TagConstants.RPAREN);
        } else
            ErrorSet.fatal(l.startingLoc, 
				"Syntax error in quantified expression.");
        GCExpr returnExpr = null;
        if (tag == TagConstants.FORALL) {
	    if (rangeExpr != null) rest = BinaryExpr.make(TagConstants.IMPLIES,
						 rangeExpr, rest, locSemi);
            returnExpr = QuantifiedExpr.make(loc, endLoc, tag, vs, rest, null);
        } else if (tag == TagConstants.EXISTS) {
	    if (rangeExpr != null) rest = BinaryExpr.make(TagConstants.AND, 
						rangeExpr, rest, locSemi);
            returnExpr = QuantifiedExpr.make(loc, endLoc, tag, vs, rest, null);
        } else if (tag == TagConstants.MAXQUANT || tag == TagConstants.MIN ||
                   tag == TagConstants.PRODUCT || tag == TagConstants.SUM) {
	    if (rangeExpr == null) {
		rangeExpr = LiteralExpr.make(TagConstants.BOOLEANLIT,
					Boolean.TRUE,Location.NULL);
	    }
            returnExpr = GeneralizedQuantifiedExpr.make(loc, endLoc, tag, 
					vs, rest, rangeExpr, null);
        } else if (tag == TagConstants.NUM_OF) {
	    if (rangeExpr != null) rest = BinaryExpr.make(TagConstants.AND, 
						rangeExpr, rest, locSemi);
            returnExpr = NumericalQuantifiedExpr.make(loc, endLoc, tag, 
					vs, rest, null);
        } else {
            Assert.fail("Illegal quantifier seen at location " + loc);
        }
        
        return returnExpr;
    }


    // Overridden methods to handle new keywords and types specific
    // to this parser.

    /**
     * Is a <code>tag</code> a PrimitiveType keyword?  Overriden to
     * add type <code>TYPE</code>.
     *
     * @param tag the tag to check.
     * @return a flag indicating if the supplied parameter is a
     * primate type.
     */
    public boolean isPrimitiveKeywordTag(int tag) {
        switch(tag) {
            case TagConstants.TYPETYPE:
            case TagConstants.REAL:
            case TagConstants.BIGINT:
                return true;

            default:
                return super.isPrimitiveKeywordTag(tag);
        }
    }

    /**
     * Parses a PrimitiveType.  Overriden to add type TYPE.  Returns
     * <code>null</code> on failure.
     * 
     * <p> PrimitiveType is one of: boolean byte short int long char
     * float double void TYPE.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed primative type.
     */
    public PrimitiveType parsePrimitiveType(Lex l) {
        int tag;

        switch (l.ttype) {
            case TagConstants.TYPETYPE: tag = TagConstants.TYPECODE; break;
            case TagConstants.REAL: tag = TagConstants.DOUBLETYPE; break;
            case TagConstants.BIGINT: tag = TagConstants.LONGTYPE; break;

            default: return super.parsePrimitiveType(l);
        }
        // get here => tag is defined
    
        int loc = l.startingLoc;
        l.getNextToken();
        return PrimitiveType.make(tag, loc);
    }

    /**
     * @param tag the tag to check.
     * @return a flag indicating if <code>tag</code> is the start of
     * an unary expression other than unary '+' or '-'.  Overridded
     * to handle new identifier-like keywords "\result" and "\lockset".
     */
    public boolean isStartOfUnaryExpressionNotPlusMinus(int tag) {
	// All previous cases apply...
	if (super.isStartOfUnaryExpressionNotPlusMinus(tag))
	    return true;

	// New Identifier-like keywords:
	if (tag == TagConstants.RES || tag == TagConstants.LS)
	    return true;

	return false;
    }


    // Special handling for parsing exsures/signals clauses.

    /**
     * Parse the formal parameter declaration (the type and name of
     * the associated exception) of an <code>exsures</code> or
     * <code>signals</code> pragma.  This is a bit complicated because
     * these expressions have an optional identifier name associated
     * with the specified Throwable type.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed formal paramater declaration.
     */
    //@ requires l.m_in != null;
    public FormalParaDecl 
            parseExsuresFormalParaDecl(/*@ non_null @*/ EscPragmaLex l) {
        int modifiers = parseModifiers(l);
        ModifierPragmaVec modifierPragmas = this.modifierPragmas;
        Type paratype = parseExsuresType(l);
        Identifier idn;
        int locId = l.startingLoc;

        if (l.ttype == TagConstants.IDENT) {
            idn = l.identifierVal;
            l.getNextToken();
        } else {
            idn = TagConstants.ExsuresIdnName;
        }
      
        // allow more modifier pragmas
        modifierPragmas = parseMoreModifierPragmas(l, modifierPragmas);
        return FormalParaDecl.make(modifiers, modifierPragmas, 
                                   idn, paratype, locId);
    }

    /**
     * Parse the type of the of an <code>exsures</code> or
     * <code>signals</code> pragma parameter.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed type declaration.
     */
    //@ requires l.m_in != null;
    //@ ensures \result.syntax;
    public /*@ non_null */ Type parseExsuresType(/*@ non_null @*/ EscPragmaLex l) {
	Type type = parseExsuresPrimitiveTypeOrTypeName(l);
	return parseBracketPairs(l, type);
    }

    /**
     * Parse the type associated with an <code>exsures</code> or
     * <code>signals</code> pragma parameter.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed type declaration.
     */
    //@ requires l.m_in != null
    //@ ensures \result.syntax
    public /*@ non_null */ Type parseExsuresPrimitiveTypeOrTypeName(/*@ non_null @*/ EscPragmaLex l) {
	Type type = parseExsuresPrimitiveType(l);
	if (type != null)
	    return type;
	else
	    return parseExsuresTypeName(l);
    }

    /**
     * Parse the primative type used in an <code>exsures</code> or
     * <code>signals</code> pragma.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed type declaration, if the type is primative.
     */
    //@ requires l.m_in != null
    //@ ensures \result != null ==> \result.syntax
    public PrimitiveType parseExsuresPrimitiveType(/*@ non_null @*/ EscPragmaLex l) {
	int tag;
	switch(l.ttype) {
            case TagConstants.TYPETYPE:tag = TagConstants.TYPECODE;    break;
            case TagConstants.REAL:    tag = TagConstants.DOUBLETYPE;  break;
            case TagConstants.BIGINT:  tag = TagConstants.LONGTYPE;    break;
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
	return PrimitiveType.make(tag, loc);
    }

    /**
     * Parse the type name used in an <code>exsures</code> or
     * <code>signals</code> pragma.
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed type declaration.
     * @equivalent parseTypeName(l);
     */
    //@ requires l.m_in != null
    //@ ensures \result.syntax
    public /*@ non_null */ TypeName parseExsuresTypeName(/*@ non_null @*/ EscPragmaLex l) {
	return parseTypeName(l);	
    }

    /**
     * Parse a FieldsOfExpr and discard it.
     *
     * <pre>
     * '\fields_of' '(' SpecExpr [ ',' Idn [ ',' StoreRefExpr ] ] ')' ';'
     * </pre>
     */
    //@ requires l.m_in != null
    public void parseFieldsOfExpr(/*@ non_null @*/ EscPragmaLex l) {
        int loc = l.startingLoc;
        int tag = TagConstants.fromIdentifier(l.identifierVal);
        Expr expr = null;
        TypeName typeName = null;
        Expr storeRefExpr = null;
        expect(l, TagConstants.LPAREN);
        expr = parsePrimaryExpression(l);
        if (l.lookahead(0) == TagConstants.COMMA) {
            typeName = parseTypeName(l);
            if (l.lookahead(0) == TagConstants.COMMA)
                parseStoreRefExpr(l);
        }
        expect(l, TagConstants.RPAREN);
        noteUnsupportedCheckableJmlPragma(loc, tag);
    }

    /**
     * Parse a StoreRef and discard it.
     */
    //@ requires l.m_in != null
    public void parseStoreRef(/*@ non_null @*/ EscPragmaLex l) {
        // StoreRefKeyword
        if (l.ttype == TagConstants.NOTHING || 
            l.ttype == TagConstants.EVERYTHING ||
            l.ttype == TagConstants.NOT_SPECIFIED ||
            l.ttype == TagConstants.PRIVATE_DATA)
            // PRIVATE_DATA recognized and discarded, unclear semantics (kiniry)
        {
            l.getNextToken();
            return;
        }
        // \fields_of ...
        if (l.ttype == TagConstants.FIELDS_OF) {
            parseFieldsOfExpr(l);
            return;
        }
        // InformalDescription
        if (l.ttype == TagConstants.INFORMALPRED_TOKEN) {
            l.getNextToken();
            return;
        }
        // StoreRefExpr
        parseStoreRefExpr(l);
    }

    /**
     * Parses an <em>optional</em> StoreRefNameSuffix and discards it.
     */
    //@ requires l.m_in != null
    public void parseStoreRefNameSuffix(/*@ non_null @*/ EscPragmaLex l) {
        // StoreRefNameSuffix ::= '.' Idn | '.' 'this' | '[' SpecArrayRefExpr ']'
        if (l.ttype == TagConstants.FIELD ||
            l.ttype == TagConstants.LSQBRACKET) {
            if (l.ttype == TagConstants.FIELD) {
                l.getNextToken();
                if (l.ttype == TagConstants.IDENT ||
                    l.ttype == TagConstants.THIS) {
                    l.getNextToken();
                    return;
                } else {
                    fail(scanner.startingLoc,
                         "storage reference name suffix be an " + 
                         "identifier or 'this'.");
                }
            } else {
                // SpecArrayRefExpr
                Expr firstExpr = parsePrimaryExpression(l);
                if (l.ttype == TagConstants.RSQBRACKET ||
                    l.ttype == TagConstants.STAR) {
                    expect(l, TagConstants.RSQBRACKET);
                    return;
                }
                if ((l.ttype == TagConstants.FIELD &&
                     l.lookahead(1) != TagConstants.FIELD) ||
                    l.ttype != TagConstants.FIELD) {
                    fail(scanner.startingLoc,
                         "A range expression in an array should be of the form '[" +
                         "<spec-expr> .. <spec-expr>]'.  Note the two dots.");
                } else {
                    // Skip two dots then parse and toss SpecExpr.
                    l.getNextToken(); l.getNextToken();
                    Expr secondExpr = parsePrimaryExpression(l);
                    expect(l, TagConstants.RSQBRACKET);
                    return;
                }
            }
        }
    }

    /**
     * Parse a StoreRefExpr and discard it
     */
    //@ requires l.m_in != null
    public void parseStoreRefExpr(/*@ non_null @*/ EscPragmaLex l) {

        // Must start with Idn | 'super' | 'this'
        if (l.ttype == TagConstants.IDENT ||
            l.ttype == TagConstants.SUPER ||
            l.ttype == TagConstants.THIS) {
            l.getNextToken();
        } else {
            fail(scanner.startingLoc,
                 "storage reference expression must start with an " + 
                 "identifier, 'super', or 'this'.");
        }
        // Optional StoreRefNameSuffix.
        parseStoreRefNameSuffix(l);
    }

    //@ requires l.m_in != null
    //@ modifies modifierPragmas
    public int parseModifiers(/*@ non_null @*/ Lex l) {
	return parseModifiers(l,false);
    }

    public int parseModifiers(/*@ non_null @*/ Lex l, boolean inModel) {
        boolean seenPragma = false;
        int modifiers = Modifiers.NONE;

        getModifierLoop:
        while(true) {
            if (l.ttype == TagConstants.MODIFIERPRAGMA) {
		// FIXME
		// This part does not seem to work, since the Pragmas are
		// lexed as IDENTs
                if (! seenPragma) { seqModifierPragma.push(); seenPragma = true; }
                seqModifierPragma.addElement(l.auxVal);
                l.getNextToken();
                continue getModifierLoop;
            } else {
                for( int i=0; i<modifierKeywords.length; i++ ) {
                    if( l.ttype == modifierKeywords[i] ) {
                        // Token is modifier keyword 
                        int modifierBit = 1<<i;
                        if( (modifiers & modifierBit) != 0 ) {
                            fail(l.startingLoc, 
				"Duplicate occurrence of modifier '"
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
                if (inModel) {
                    int tag = l.ttype;
                    if (tag == TagConstants.IDENT)
                        tag = TagConstants.fromIdentifier(l.identifierVal);
                    if (tag == TagConstants.PURE) {
			modifiers |= Modifiers.ACC_PURE;
			l.getNextToken();
			continue getModifierLoop;
                    }		
                    if (tag == TagConstants.HELPER) {
			modifiers |= Modifiers.ACC_HELPER;
			l.getNextToken();
			continue getModifierLoop;
                    }		
                    if (tag == TagConstants.NON_NULL) {
			// FIXME _ What do we do with it?
			l.getNextToken();
			continue getModifierLoop;
                    }
                    if (tag == TagConstants.INSTANCE) {
			// FIXME _ What do we do with it?
			l.getNextToken();
			continue getModifierLoop;
                    }
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

    private boolean argListInAnnotation = false;
    public FormalParaDeclVec parseFormalParameterList(Lex l) {
	/* Should be on LPAREN */
	if (l.ttype != TagConstants.LPAREN)
	    fail(l.startingLoc, "Expected open paren");
	if (l.lookahead(1) == TagConstants.RPAREN ) {
	    // Empty parameter list
	    expect( l, TagConstants.LPAREN);
	    expect( l, TagConstants.RPAREN);
	    return FormalParaDeclVec.make();
	} else {
	    seqFormalParaDecl.push();
	    while ( l.ttype != TagConstants.RPAREN ) {
		l.getNextToken();	// swallow COMMA
		int modifiers = parseModifiers(l);
		ModifierPragmaVec modifierPragmas = this.modifierPragmas;
		int typeLoc = l.startingLoc;
		Type type = parseType(l);
		Identifier id = null;
		if (argListInAnnotation && type instanceof TypeName &&
			((TypeName)type).name.printName().equals("non_null") &&
			!(  l.ttype == TagConstants.IDENT &&
			    (l.lookahead(1) == TagConstants.COMMA ||
			    l.lookahead(1) == TagConstants.RPAREN))) {
		    // The non_null is a modifier, not a type
		    // [ A model method or constructor does not need to 
		    //   enclose the 'non_null' in annotation markers; hence
		    //   we can have either 'non_null i' in which non_null
		    //   is a type or 'non_null int i' in which non_null is
		    //   a modifier.]
		    type = parseType(l);
		    if (modifierPragmas == null)
			modifierPragmas = ModifierPragmaVec.make();
		    modifierPragmas.addElement(SimpleModifierPragma.make(
				TagConstants.NON_NULL,typeLoc));
		}
		int locId = l.startingLoc;
		if (id == null) id = parseIdentifier(l);
		type = parseBracketPairs(l, type);
		modifierPragmas = parseMoreModifierPragmas(l, modifierPragmas);
		seqFormalParaDecl.addElement( FormalParaDecl.make(modifiers,
			modifierPragmas, id, type, locId));
		if (l.ttype != TagConstants.RPAREN && l.ttype != TagConstants.COMMA)
		    fail(l.startingLoc, "Exprected comma or close paren");
	    }
	    expect(l, TagConstants.RPAREN);
	    return FormalParaDeclVec.popFromStackVector(seqFormalParaDecl);
	}
    }
} // end of class EscPragmaParser

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */
