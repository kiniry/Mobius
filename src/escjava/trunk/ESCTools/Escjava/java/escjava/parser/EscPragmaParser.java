/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.parser;

import escjava.Main;
import escjava.ast.*;
// This import is necessary to override javafe.ast.TagConstants.
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;

import java.io.IOException;

import javafe.ast.*;
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


 DurationClause ::= DurationKeyword '\not_specified' [';']
 | DurationKeyword DurSpecExpr [ 'if' predicate ] [';']

 DurSpecExpr ::= SpecExpr (of type int) OpWithIntResult DurSpecExpr
 | '\duration' '(' MethodInvOrConstructor ')' IntOp DurSpecExpr

 SpaceExpr ::= '\space' '(' MethodInvOrConstructor ')'

 WorkingSpaceClause ::= WorkingSpaceKeyword '\not_specified' [';']
 | WorkingSpaceKeyword WorkingSpaceSpecExpr [ 'if' predicate ] [';']

 WorkingSpaceSpecExpr ::= SpecExpr (of type int) OpWithIntResult WorkingSpaceSpecExpr
 | '\working_space' '(' MethodInvOrConstructor ')' IntOp WorkingSpaceSpecExpr

 MethodInvOrConstructor ::= MethodInvocation | ConstructorInvocation

 OpWithIntResult ::= STAR | '/' | '%' | PLUS | '-' | '&' | BITOR | '^'

 WorkingSpaceKeyword ::= 'working_space' | 'working_space_redundantly'

 DurationKeyword ::= 'duration' | 'duration_redundantly'

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

 JmlSpecExpr ::= '\nothing' | '\everything'

 Function ::= '\fresh' | '\nonnullelements' | '\elemtype' | '\max' | '\old'
 | '\typeof'

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
 * @todo kiniry 29 Apr 2003 - Why are the types of all duration/space
 * expressions int instead of long?
 *
 * @see escjava.Main.checkRedundantSpecs
 */

public class EscPragmaParser extends Parse implements PragmaParser
{
    private static final boolean DEBUG = false;
    
    /** 
     * The informal-predicate decoration is associated with a
     * true-valued boolean literal expression, if the concrete syntax
     * of this expression was an informal comment.  The value
     * associated with the decoration is the string of the informal
     * predicate (i.e., the comment itself).
     */
    public static final ASTDecoration informalPredicateDecoration =
        new ASTDecoration("informalPredicate");

    /**
     * The lexer associated with this pragma parser from which we
     * will read tokens.
     */
    private /*@ non_null @*/ EscPragmaLex scanner;

    public int NOTHING_ELSE_TO_PROCESS = -2;
    public int NEXT_TOKEN_STARTS_NEW_PRAGMA = -1;

    /** 
     * The value NOTHING_ELSE_TO_PROCESS means there is nothing else
     * to process.  The value NEXT_TOKEN_STARTS_NEW_PRAGMA means there
     * is something to process and the next thing to read begins a new
     * pragma (or ends the pragma-containing comment).  The other
     * values indicate that the pragma parser is in the middle of
     * parsing some pragma, and is expected to continue this parsing
     * next time it gets control.
     */
    private int inProcessTag;
    /*@ invariant inProcessTag == NOTHING_ELSE_TO_PROCESS || 
     @           inProcessTag == NEXT_TOKEN_STARTS_NEW_PRAGMA ||
     @           inProcessTag == TagConstants.STILL_DEFERRED ||
     @           inProcessTag == TagConstants.MONITORED_BY ||
     @           inProcessTag == TagConstants.MODIFIES ||
     @           inProcessTag == TagConstants.ALSO_MODIFIES ||
     @           inProcessTag == TagConstants.JML_MODIFIABLE ||
     @           inProcessTag == TagConstants.JML_ASSIGNABLE ||
     @           inProcessTag == TagConstants.LOOP_PREDICATE ||
     @           inProcessTag == TagConstants.JML_ALSO; 
     @*/

    private int inProcessLoc;
    private CorrelatedReader pendingJavadocComment;

    /**
     * Maximum # of levels of nesting of annotation comments allowed.
     * 0 == no nesting of annotation comments allowed.
     * 
     * <p> If you change this, change the error message in
     * EscPragmaParser(int) below as well.
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
	scanner.addPunctuation("<-", TagConstants.JML_LEFTARROW);
	scanner.addPunctuation("->", TagConstants.JML_RIGHTARROW);
	scanner.addPunctuation("{|", TagConstants.JML_OPENPRAGMA);
	scanner.addPunctuation("|}", TagConstants.JML_CLOSEPRAGMA);
	addOperator(TagConstants.IMPLIES, 76, false);
	addOperator(TagConstants.EXPLIES, 76, true);
	addOperator(TagConstants.IFF, 73, true);
	addOperator(TagConstants.NIFF, 73, true);
	addOperator(TagConstants.SUBTYPE, 140, true);
	addOperator(TagConstants.DOTDOT, 1, true);
	scanner.addKeyword("\\result", TagConstants.RES);
	scanner.addKeyword("\\lockset", TagConstants.LS);
	scanner.addKeyword("\\TYPE", TagConstants.TYPETYPE);
	scanner.addKeyword("\\everything",TagConstants.JML_EVERYTHING);
	scanner.addKeyword("\\nothing",TagConstants.JML_NOTHING);
	scanner.addKeyword("\\not_specified",TagConstants.JML_NOT_SPECIFIED);
	scanner.addKeyword("\\such_that",TagConstants.JML_SUCH_THAT);
	inProcessTag = NOTHING_ELSE_TO_PROCESS;
    }

    /**
     * @param tag the comment tag character to check.
     * @return true iff tag is an '@' or an '*' character.
     */
    public boolean checkTag(int tag) {
	if (Main.parsePlus && tag == '+') return true;
        return tag == '@' || tag == '*' ;
    }

    /**
     * Restart a pragma parser on a new input stream.  If
     * <code>this</code> is already opened on another {@link
     * CorrelatedReader}, close the old reader.
     *
     * @param in the reader from which to read.
     * @param eolComment a flag that indicates we are parsing an EOL
     * comment (a comment that starts with "//").
     */
    public void restart(CorrelatedReader /*@ non_null @*/ in, 
                        boolean eolComment) {
        try {
            int c = in.read();
            // System.out.println("restart: c = '"+(char)c+"'");

	    if (Main.parsePlus && c == '+') c = in.read();
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
                    Assert.fail("Bad starting character on comment:"+ c + " " + (char)c);
            }
        } catch (IOException e) {
            ErrorSet.fatal(in.getLocation(), e.toString());
        }
    }

    /**
     * Parse embedded <esc> ... </esc> in Javadoc comments.
     *
     * @return a flag indicating if an embedded comment was recognized.
     * @exception IOException if something goes wrong during reading.
     */
    private boolean processJavadocComment() throws IOException {
        if (pendingJavadocComment == null) {
            return false;
        }

        final String startEnclosedPragma = "<esc>";
        final String endEnclosedPragma = "</esc>";

        int startLoc = scanFor(pendingJavadocComment, startEnclosedPragma);
        if (startLoc == Location.NULL) {
            pendingJavadocComment = null;
            inProcessTag = NOTHING_ELSE_TO_PROCESS;
            return false;
        }

        // Mark the current character, the first character inside the enclosed
        // pragma:
        pendingJavadocComment.mark();

        if (scanFor(pendingJavadocComment, endEnclosedPragma) != Location.NULL) {
            // Restrict "pendingJavadocComment" to just before endEnclosedPragma
            CorrelatedReader nu =
                pendingJavadocComment.createReaderFromMark(endEnclosedPragma.length());
            nu = new JmlCorrelatedReader(nu, JmlCorrelatedReader.JAVADOC_COMMENT);
            scanner.restart(nu);
            inProcessTag = NEXT_TOKEN_STARTS_NEW_PRAGMA;
            return true;
        } else {
            ErrorSet.error(startLoc,
                           "Pragma in javadoc comment is not correctly " +
                           "terminated (missing " + endEnclosedPragma + ")");
            pendingJavadocComment = null;
            inProcessTag = NOTHING_ELSE_TO_PROCESS;
            return false;
        }
    } //@ nowarn Exception // IndexOutOfBoundsException

    /**
     * Eat any wizard inserted comment at the start of an escjava
     * annotation.
     *
     * <p> May side-effect the mark of <code>in</code>.
     *
     * <p> Eats "([^)]*)", if present, from <code>in</code>.
     *
     * @param in the stream from which to read.
     */
    private void eatWizardComment(CorrelatedReader /*@ non_null @*/ in) 
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
     * <code>match</code>. Only works if the first character is not
     * repeated in the string.
     *
     * <p> If present, the location of the match is returned.  If not
     * present, <code>Location.NULL</code> is returned.
     *
     * <p> Requires that <code>in</code> is not closed.
     *
     * @param in the stream from which to read.
     * @param match the string to match against the input stream.
     * @return the location of the match, or
     * <code>Location.NULL</code> if there is no match.
     */
    private int scanFor(CorrelatedReader /*@ non_null @*/ in,
			String /*@ non_null @*/ match)
            throws IOException
    {

	int start = match.charAt(0);
	int c = in.read();
	
        mainLoop:
	for(;;) {
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
	    
    /**
     * Closes this pragma parser including its scanner and pending
     * Javadoc comment.
     */
    public void close() {
	scanner.close();
	if (pendingJavadocComment != null) {
            pendingJavadocComment.close();
            pendingJavadocComment = null;
	}
    }

    /**
     * Parse the next pragma, putting information about it in the
     * provided token <code>dst</code>, and return a flag indicating if
     * there are further pragmas to be parsed.
     *
     * Note: All worrying about 'also' is now done during the desugaring
     * of specs.  JML style of using also is preferred.
     *
     * @param dst the token in which to store information about the
     * current pragma.
     * @return a flag indicating if further pragmas need to be parsed.
     * @see Lex
     */
    public boolean getNextPragma(Token /*@ non_null @*/ dst) {
        try {
            if (inProcessTag == NOTHING_ELSE_TO_PROCESS) {
                if (DEBUG)
                    Info.out("getNextPragma: Nothing else to process.");
                return false;
            }

            // See if we need to continue a previous pragma, for example
            // "monitored_by", which can take multiple SpecExprs
            if ((inProcessTag != NEXT_TOKEN_STARTS_NEW_PRAGMA) &&
                (inProcessTag != TagConstants.JML_ALSO)) { 
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
            if (Main.parsePlus &&
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
                case TagConstants.JML_BEHAVIOR:
                case TagConstants.JML_NORMAL_BEHAVIOR:
                case TagConstants.JML_EXCEPTIONAL_BEHAVIOR:
		/* All desugaring of normal and exceptional behavior is now
		   performed in the desugaring step in AnnotationHandler.
		*/
                   dst.ttype = TagConstants.MODIFIERPRAGMA;
                   dst.auxVal = SimpleModifierPragma.make(tag, loc);
                   break;

                case TagConstants.NOWARN:
                    dst.ttype = TagConstants.LEXICALPRAGMA;
                    seqIdentifier.push();
                    if (scanner.ttype == TagConstants.IDENT)
                        for (;;) {
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

                case TagConstants.STILL_DEFERRED:
                case TagConstants.MONITORED_BY:
                case TagConstants.MODIFIES:
                case TagConstants.ALSO_MODIFIES:
                case TagConstants.JML_MODIFIABLE:
                case TagConstants.JML_MEASURED_BY: 
                case TagConstants.JML_ASSIGNABLE:
                case TagConstants.JML_MODIFIABLE_REDUNDANTLY:
                case TagConstants.JML_ASSIGNABLE_REDUNDANTLY:
                case TagConstants.JML_MODIFIES_REDUNDANTLY:
                case TagConstants.JML_MEASURED_BY_REDUNDANTLY:
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    if (DEBUG)
                        Info.out("getNextPragma: parsed a 'modifiable': " + 
                                 dst.ztoString());
		    if (isRedundant(tag) &&
                        (! Main.checkRedundantSpecs)) {
                        // toss the results of this pragma parse and
                        // return the next parsed pragma expression.
                        return getNextPragma(dst);
                    }
                    return true;

                case TagConstants.JML_DEPENDS_REDUNDANTLY:    // SC AAST 4
                case TagConstants.JML_DEPENDS: {               // SC AAST 4
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    Expr target = parsePrimaryExpression(scanner);
                    int locOp = scanner.startingLoc;
		    expect(scanner, TagConstants.JML_LEFTARROW);
		    Vector list = new Vector();
		    while (true) {
			Expr value = parseExpression(scanner);
			list.add(value);
			if (scanner.ttype != TagConstants.COMMA) break;
			scanner.getNextToken();
		    }
		    dst.auxVal = DependsPragma.make(tag,target,
			ExprVec.make(list), loc);
		    if (tag == TagConstants.JML_DEPENDS_REDUNDANTLY &&
                        (! Main.checkRedundantSpecs)) {
                        // toss the results of this pragma parse and
                        // return the next parsed pragma expression.
                        return getNextPragma(dst);
                    }
		    semiNotOptional = true;
                    break;
		}

                case TagConstants.UNREACHABLE:
                    dst.ttype = TagConstants.STMTPRAGMA;
                    dst.auxVal = SimpleStmtPragma.make(tag, loc);
                    if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
                    break;
	
                case TagConstants.ASSERT:
                case TagConstants.JML_ASSERT_REDUNDANTLY:
                case TagConstants.ASSUME:
                case TagConstants.JML_ASSUME_REDUNDANTLY:
                case TagConstants.LOOP_INVARIANT:
                case TagConstants.JML_LOOP_INVARIANT_REDUNDANTLY:
                case TagConstants.JML_MAINTAINING:
                case TagConstants.JML_MAINTAINING_REDUNDANTLY:
                case TagConstants.DECREASES:
                case TagConstants.JML_DECREASES_REDUNDANTLY:
                case TagConstants.JML_DECREASING:
                case TagConstants.JML_DECREASING_REDUNDANTLY:
                    dst.ttype = TagConstants.STMTPRAGMA;
                    dst.auxVal = ExprStmtPragma.make(tag, parseExpression(scanner), loc);
		    if (isRedundant(tag) &&
                        (! Main.checkRedundantSpecs)) {
                        // eat non-optional semicolon and return the
                        // next parsed pragma expression.
                        eatSemiColon(kw);
                        return getNextPragma(dst);
                    }
                    semiNotOptional = true;
                    break;

                case TagConstants.LOOP_PREDICATE:
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    semiNotOptional = true;
                    if (DEBUG)
                        Info.out("getNextPragma: parsed a loop predicate: " + 
                                 dst.ztoString());
                    return true;	  

                case TagConstants.SET:
                    {
		    dst.ttype = TagConstants.STMTPRAGMA;
                    Expr target = parsePrimaryExpression(scanner);
                    int locOp = scanner.startingLoc;
                    expect(scanner, TagConstants.ASSIGN);
                    Expr value = parseExpression(scanner);
                    dst.auxVal = SetStmtPragma.make(target, locOp, value, loc);
                    semiNotOptional = true;
		    }
                    break;

                case TagConstants.JML_REPRESENTS:             // SC HPT AAST 4
		    {
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    Expr target = parsePrimaryExpression(scanner);
                    int locOp = scanner.startingLoc;
		    if (scanner.ttype == TagConstants.JML_LEFTARROW) {
			expect(scanner, TagConstants.JML_LEFTARROW);
			Expr value = parseExpression(scanner);
			dst.auxVal = ExprDeclPragma.make(tag, BinaryExpr.make(TagConstants.EQ, target, value, locOp) , loc);
		    } else if (scanner.ttype == TagConstants.JML_SUCH_THAT) {
			expect(scanner, TagConstants.JML_SUCH_THAT);
			Expr value = parseExpression(scanner);
			dst.auxVal = ExprDeclPragma.make(tag, value, loc);
		    }
                    semiNotOptional = true;
		    }
                    break;

                case TagConstants.AXIOM:
		case TagConstants.JML_INITIALLY:
                case TagConstants.INVARIANT:
                case TagConstants.JML_INVARIANT_REDUNDANTLY:
		case TagConstants.JML_CONSTRAINT:
		case TagConstants.JML_CONSTRAINT_REDUNDANTLY:
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    dst.auxVal = ExprDeclPragma.make(tag, parseExpression(scanner), loc);
                    if (isRedundant(tag) &&
                        (! Main.checkRedundantSpecs)) {
                        // eat non-optional semicolon and return the
                        // next parsed pragma expression.
                        eatSemiColon(kw);
                        return getNextPragma(dst);
                    }
                    semiNotOptional = true;
                    break;

		case TagConstants.IMPORT:
			ErrorSet.caution(loc,"An import statement in an annotation should begin with 'model import'");
			scanner.lexicalPragmas.addElement( 
			    ImportPragma.make(parseImportDeclaration(scanner),
						 loc));
			semiNotOptional = true;
			return getNextPragma(dst);

                case TagConstants.JML_MODEL:
		    if (scanner.lookahead(0) == TagConstants.IMPORT) {
			scanner.lexicalPragmas.addElement( 
			    ImportPragma.make(parseImportDeclaration(scanner),
						 loc));
			semiNotOptional = true;
			return getNextPragma(dst);
		    }
		    prefixModifiers |= Modifiers.ACC_MODEL;
                case TagConstants.GHOST:
                    {
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
	      
                    int locId     = scanner.startingLoc;
                    Identifier id = parseIdentifier(scanner);
                    Type vartype = parseBracketPairs(scanner, type);
	      
                    VarInit init = null;
                    int locAssignOp = Location.NULL;
		    if (scanner.ttype == TagConstants.LPAREN) {
			if (tag == TagConstants.GHOST) {
			    ErrorSet.error(loc,
				"A method may not be declared ghost");
			}
			// Must be a model method
			// FIXME - note - cannot have a ghost method
			FormalParaDeclVec args = parseFormalParameterList(scanner);
			int locThrowsKeyword;
			if (scanner.ttype == TagConstants.THROWS) {
			    locThrowsKeyword = scanner.startingLoc;
			} else {
			    locThrowsKeyword = Location.NULL;
			}
			TypeNameVec raises = parseTypeNames(scanner, TagConstants.THROWS);
			int locOpenBrace = Location.NULL;
			BlockStmt body = null;
			if (scanner.ttype == TagConstants.SEMICOLON) {
			    scanner.getNextToken(); // eats semicolon
			} else if (scanner.ttype == TagConstants.LBRACE) {
			    locOpenBrace = scanner.startingLoc;
			    body = parseBlock(scanner, true);
			// FIXME - the above parses with specOnly=true which will not provide the body
			} else {
			// FIXME -- error
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
			if (scanner.ttype == TagConstants.ASSIGN) {
			    locAssignOp = scanner.startingLoc;
			    scanner.getNextToken();
			    init = parseVariableInitializer(scanner, false);
			}
			FieldDecl decl
			    = FieldDecl.make(modifiers, modifierPragmas, 
					     id, vartype, locId, init, locAssignOp );
		  
			if (scanner.ttype == TagConstants.MODIFIERPRAGMA
			    || scanner.ttype == TagConstants.SEMICOLON ) {
			    // if modifier pragma, retroactively add to modifierPragmas
			    parseMoreModifierPragmas(scanner, modifierPragmas);
			}
		  
			if (scanner.ttype == TagConstants.COMMA)
			    fail(scanner.startingLoc,
				 "Only one field may be declared per ghost or model annotation.");
		  
			if (tag == TagConstants.GHOST) {
			    dst.auxVal = GhostDeclPragma.make(decl, loc);
			} else if (tag == TagConstants.JML_MODEL) {
			    dst.auxVal = ModelDeclPragma.make(decl, loc);
			}
			semiNotOptional = true;
// FIXME - monitored_by as well??
// FIXME - test this without replciating the string
			if (scanner.ttype == TagConstants.IDENT &&
			    scanner.identifierVal.toString().equals("initially")) {
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
                    
                    loop:
                    for(;;) {
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

                    dst.auxVal = SkolemConstantPragma.make(v, locType, scanner.startingLoc);
                    semiNotOptional = true;
                    break;
                }

                case TagConstants.UNINITIALIZED:
                case TagConstants.MONITORED:
                case TagConstants.NON_NULL:
                case TagConstants.JML_INSTANCE:
                case TagConstants.JML_PURE:
                case TagConstants.SPEC_PUBLIC:
                case TagConstants.JML_SPEC_PROTECTED: // SC HPT AAST 3
                case TagConstants.WRITABLE_DEFERRED:
                case TagConstants.HELPER:
		case TagConstants.JML_OPENPRAGMA:
		case TagConstants.JML_CLOSEPRAGMA:
		case TagConstants.JML_IMPLIES_THAT:
		case TagConstants.JML_FOR_EXAMPLE:
		case TagConstants.JML_EXAMPLE:
		case TagConstants.JML_NORMAL_EXAMPLE:
		case TagConstants.JML_EXCEPTIONAL_EXAMPLE:
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal = SimpleModifierPragma.make(tag, loc);
                    break;

                case TagConstants.READABLE_IF:
                case TagConstants.WRITABLE_IF:
                case TagConstants.REQUIRES:
                case TagConstants.JML_REQUIRES_REDUNDANTLY:
                case TagConstants.ALSO_REQUIRES:
                case TagConstants.ENSURES:
                case TagConstants.JML_ENSURES_REDUNDANTLY:
                case TagConstants.ALSO_ENSURES:
                case TagConstants.JML_PRE:
                case TagConstants.JML_PRE_REDUNDANTLY:
                case TagConstants.JML_POST:
                case TagConstants.JML_POST_REDUNDANTLY:
		case TagConstants.JML_DIVERGES:
		case TagConstants.JML_DIVERGES_REDUNDANTLY:
                case TagConstants.JML_WHEN_REDUNDANTLY:       // NOT SC concurrent only
                case TagConstants.JML_WHEN:                   // NOT SC concurrent only
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
		    dst.auxVal
			= ExprModifierPragma.make(tag, parseExpression(scanner), loc);
		    if (isRedundant(tag) &&
                        (! Main.checkRedundantSpecs)) {
                        // eat non-optional semicolon and return the
                        // next parsed pragma expression.
                        eatSemiColon(kw);
                        return getNextPragma(dst);
                    }
                    semiNotOptional = true;
                    break;

                case TagConstants.JML_ALSO:
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal = SimpleModifierPragma.make(tag, loc);
		    break;

                case TagConstants.EXSURES:
                case TagConstants.JML_EXSURES_REDUNDANTLY:
                case TagConstants.ALSO_EXSURES:
                case TagConstants.JML_SIGNALS:
                case TagConstants.JML_SIGNALS_REDUNDANTLY:
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
		    dst.auxVal
                            = VarExprModifierPragma.make(tag, arg, expr, loc);
                    if (((tag == TagConstants.JML_EXSURES_REDUNDANTLY) ||
                         (tag == TagConstants.JML_SIGNALS_REDUNDANTLY)) &&
                        (! Main.checkRedundantSpecs)) {
                        // eat non-optional semicolon and return the
                        // next parsed pragma expression.
                        eatSemiColon(kw);
                        return getNextPragma(dst);
                    }
                    semiNotOptional = true;
                    break;

                case TagConstants.JML_WACK_DURATION:        // SC HPT 2
                case TagConstants.JML_SPACE:                // SC HPT 2
                case TagConstants.JML_WACK_WORKING_SPACE:   // SC HPT 2
                    ErrorSet.fatal(loc, "Unsupported pragma: " + 
                                   TagConstants.toString(tag) +
                                   "; kiniry@users.sf.net is working on it.");
                    break;

                case TagConstants.JML_DURATION_REDUNDANTLY:   // SC HPT 2
                case TagConstants.JML_DURATION:               // SC HPT 2
                case TagConstants.JML_WORKING_SPACE_REDUNDANTLY:// SC HPT 2
                case TagConstants.JML_WORKING_SPACE:            // SC HPT 2
                    ErrorSet.fatal(loc, "Unsupported pragma: " + 
                                   TagConstants.toString(tag) +
                                   "; kiniry@users.sf.net is working on it.");
                    break;

                case TagConstants.JML_MIN:                  // SC HPT AAST 3
                case TagConstants.JML_PRODUCT:              // SC HPT AAST 3
                case TagConstants.JML_SUM:                  // SC HPT AAST 3
                case TagConstants.JML_NUM_OF:               // SC AAST 3
                    ErrorSet.fatal(loc, "Unsupported pragma: " + 
                                   TagConstants.toString(tag) +
                                   "; kiniry@users.sf.net is working on it.");
                    break;

                // 'SC' == Statically Checkable or otherwise useful
                // 'HPT' == Handle at Parse-time 'AAST' == 'Augments
                // Abstract Symbol Tree' Final 0-5 indicates
                // difficulty of implementation; 0 being easiest.  All
                // estimates and implementation/design guesses were
                // made by Joe Kiniry on 29 April 2003.

                // Unsupported JML keywords beginning with '\' (wack)
                case TagConstants.JML_FIELDS_OF:            // SC AAST 4
                    // unknown exact semantics
                case TagConstants.JML_INVARIANT_FOR:        // SC AAST 4
                case TagConstants.JML_IS_INITIALIZED:       // SC AAST 3
                case TagConstants.JML_NOT_MODIFIED:         // SC AAST 4
                case TagConstants.JML_NOT_SPECIFIED:        // HPT? 2
                case TagConstants.JML_OTHER:                // unclean semantics
                case TagConstants.JML_PRIVATE_DATA:         // unclear semantics
                case TagConstants.JML_REACH:                // SC HPT AAST 5
                    
                // Unsupported JML keywords not beginning with '\' (wack).
                case TagConstants.JML_ABRUPT_BEHAVIOR:        // unclear semantics
                case TagConstants.JML_ACCESSIBLE_REDUNDANTLY: // SC HPT AAST 2
                case TagConstants.JML_ACCESSIBLE:             // SC HPT AAST 2
                // case TagConstants.JML_ALSO: support complete (kiniry)
                // case TagConstants.JML_ASSERT_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_ASSIGNABLE_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_ASSIGNABLE: support complete (kiniry)
                // case TagConstants.JML_ASSUME_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_BEHAVIOR: support complete (kiniry)
                case TagConstants.JML_BREAKS_REDUNDANTLY:     // unclear semantics
                case TagConstants.JML_BREAKS:                 // unclear semantics
                case TagConstants.JML_CALLABLE_REDUNDANTLY:   // unclear semantics
                case TagConstants.JML_CALLABLE:               // unclear semantics
                case TagConstants.JML_CHOOSE_IF:              // unclear semantics
                case TagConstants.JML_CHOOSE:                 // unclear semantics
                // case TagConstants.JML_CONSTRAINT_REDUNDANTLY: // SC AAST 4 // parsed - cok
                // case TagConstants.JML_CONSTRAINT:             // SC AAST 4 // parsed - cok
                case TagConstants.JML_CONTINUES_REDUNDANTLY:  // unclear semantics
                case TagConstants.JML_CONTINUES:              // unclear semantics
                // case TagConstants.JML_DECREASES_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_DECREASING_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_DECREASING: support complete (kiniry)
                //case TagConstants.JML_DEPENDS_REDUNDANTLY:    // SC AAST 4 // Parsed (cok)
                //case TagConstants.JML_DEPENDS:                // SC AAST 4 // Parsed (cok)
                //case TagConstants.JML_DIVERGES_REDUNDANTLY:   // Parsed (cok)
                //case TagConstants.JML_DIVERGES:               // parsed (cok)
                // case TagConstants.JML_ENSURES_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_EXAMPLE:                // NOT SC // parsed - cok
                // case TagConstants.JML_EXCEPTIONAL_BEHAVIOR: support complete (kiniry)
                // case TagConstants.JML_EXCEPTIONAL_EXAMPLE:    // NOT SC - parsed cok
                // case TagConstants.JML_EXSURES_REDUNDANTLY: support complete (kiniry)
                case TagConstants.JML_FORALL:                 // unclear semantics
                // case TagConstants.JML_FOR_EXAMPLE:            // NOT SC // parsed - cok
                //case TagConstants.JML_IMPLIES_THAT:           // NOT SC // parsed - cok
                case TagConstants.JML_HENCE_BY_REDUNDANTLY:   // unclear semantics
                case TagConstants.JML_HENCE_BY:               // unclear semantics
                case TagConstants.JML_INITIALIZER:            // SC AAST 4
                // case TagConstants.JML_INITIALLY:              // SC AAST 4 // parsed - cok
                // case TagConstants.JML_INSTANCE: parses but no semantics (cok) SC AAST 3
                // case TagConstants.JML_INVARIANT_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_LOOP_INVARIANT_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_MAINTAINING_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_MAINTAINING: support complete (kiniry)
                //case TagConstants.JML_MEASURED_BY_REDUNDANTLY:// unclear semantics (parsed - cok)
                //case TagConstants.JML_MEASURED_BY:            // unclear semantics (parsed - cok)
                case TagConstants.JML_MODEL_PROGRAM:          // unclear semantics
                // case TagConstants.JML_MODIFIABLE_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_MODIFIABLE: support complete (kiniry)
                // case TagConstants.JML_MODIFIES_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_NORMAL_BEHAVIOR: support complete (kiniry)
                // case TagConstants.JML_NORMAL_EXAMPLE:         // NOT SC // parsed cok
                case TagConstants.JML_OLD:                    // unclear semantics
                case TagConstants.JML_OR:                     // unclear semantics
                // case TagConstants.JML_POST_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_POST: support complete (kiniry)
                // case TagConstants.JML_PRE_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_PRE: support complete (kiniry)
                // case TagConstants.JML_PURE: support complete (cok)
                case TagConstants.JML_REFINE:                 // SC HPT AAST 3
                case TagConstants.JML_REPRESENTS_REDUNDANTLY: // SC HPT AAST 4
                // case TagConstants.JML_REQUIRES_REDUNDANTLY: support complete (kiniry)
                case TagConstants.JML_RETURNS_REDUNDANTLY:    // unclear semantics
                case TagConstants.JML_RETURNS:                // unclear semantics
                // case TagConstants.JML_SIGNALS_REDUNDANTLY: support complete (kiniry)
                // case TagConstants.JML_SIGNALS: support complete (kiniry)
                case TagConstants.JML_STATIC_INITIALIZER:     // SC AAST 4
                case TagConstants.JML_SUBCLASSING_CONTRACT:   // NOT SC
                case TagConstants.JML_WEAKLY:                 // unclear semantics
                //case TagConstants.JML_WHEN_REDUNDANTLY:       // NOT SC concurrent only (parsed - cok)
                //case TagConstants.JML_WHEN:                   // NOT SC concurrent only (parsed - cok)
                    ErrorSet.fatal(loc, "Unsupported pragma: " + 
                                   TagConstants.toString(tag));
                    break;
	
                default:
                    ErrorSet.fatal(loc, "Unrecognized pragma: " + tag + " " +
                                   TagConstants.toString(tag));
            }

            if (semiNotOptional)
                eatSemiColon(kw);
            if (DEBUG)
                Info.out("getNextPragma: parsed : " + dst.ztoString());
            return true;
        } catch (IOException e) { 
            return false; 
        }
    }

    private void eatSemiColon(Identifier kw) {
        if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
        else if (scanner.ttype != TagConstants.EOF)
            ErrorSet.fatal(scanner.startingLoc, 
                           ("Semicolon required when a " + kw.toString()
                            + " pragma is followed by another pragma."));
    }

    /*@ requires inProcessTag == TagConstants.STILL_DEFERRED ||
      @          inProcessTag == TagConstants.MONITORED_BY ||
      @          inProcessTag == TagConstants.MODIFIES ||
      @          inProcessTag == TagConstants.JML_MODIFIES_REDUNDANTLY ||
      @          inProcessTag == TagConstants.ALSO_MODIFIES ||
      @          inProcessTag == TagConstants.JML_MODIFIABLE ||
      @          inProcessTag == JML_MODIFIABLE_REDUNDANTLY ||
      @          inProcessTag == TagConstants.JML_ASSIGNABLE ||
      @          inProcessTag == JML_ASSIGNABLE_REDUNDANTLY ||
      @          inProcessTag == TagConstants.LOOP_PREDICATE;
      @*/
    //@ requires scanner.startingLoc != Location.NULL;
    //@ requires scanner.m_in != null;
    private void continuePragma(Token /*@ non_null @*/ dst) throws IOException {
        if (inProcessTag == TagConstants.STILL_DEFERRED) {
            int locId = scanner.startingLoc;
            Identifier idn = parseIdentifier(scanner);
            dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
            dst.auxVal = StillDeferredDeclPragma.make(idn, inProcessLoc, locId);
        } else if (inProcessTag == TagConstants.MONITORED_BY ) {
            dst.startingLoc = inProcessLoc;
	    int tempInProcessTag = inProcessTag;
	    int t = scanner.lookahead(0);
	    if (t == TagConstants.JML_NOTHING) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
		    NothingExpr.make(scanner.startingLoc), inProcessLoc);
	    } else if (t == TagConstants.JML_NOT_SPECIFIED) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
		    NotSpecifiedExpr.make(scanner.startingLoc), inProcessLoc);
	    } else if (t == TagConstants.JML_EVERYTHING) {
		scanner.getNextToken();
		dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
		    EverythingExpr.make(scanner.startingLoc), inProcessLoc);
	    } else {	
	        Expr e = parseExpression(scanner);
                dst.auxVal = ExprModifierPragma.make(tempInProcessTag, 
			e, inProcessLoc);
            }
            dst.ttype = TagConstants.MODIFIERPRAGMA;
        } else if (inProcessTag == TagConstants.MODIFIES ||
                   inProcessTag == TagConstants.JML_MODIFIES_REDUNDANTLY ||
                   inProcessTag == TagConstants.ALSO_MODIFIES ||
                   inProcessTag == TagConstants.JML_MODIFIABLE ||
                   inProcessTag == TagConstants.JML_MODIFIABLE_REDUNDANTLY ||
                   inProcessTag == TagConstants.JML_MEASURED_BY ||
                   inProcessTag == TagConstants.JML_MEASURED_BY_REDUNDANTLY ||
                   inProcessTag == TagConstants.JML_ASSIGNABLE ||
		   inProcessTag == TagConstants.JML_ASSIGNABLE_REDUNDANTLY) {
            dst.startingLoc = inProcessLoc;
	    int tempInProcessTag = inProcessTag;
	    int t = scanner.lookahead(0);
	    Expr e = null;
	    if (t == TagConstants.JML_NOTHING) {
		scanner.getNextToken();
		e = NothingExpr.make(scanner.startingLoc);
	    } else if (t == TagConstants.JML_NOT_SPECIFIED) {
		scanner.getNextToken();
		e = NotSpecifiedExpr.make(scanner.startingLoc);
	    } else if (t == TagConstants.JML_EVERYTHING) {
		scanner.getNextToken();
		e = EverythingExpr.make(scanner.startingLoc);
	    } else {	
	        e = parseExpression(scanner);
            }
	    t = scanner.ttype;
	    Expr cond = null;
	    if (t == TagConstants.IF) {
		scanner.getNextToken();
		cond = parseExpression(scanner);
	    }
	    dst.auxVal = CondExprModifierPragma.make(tempInProcessTag, 
			e, inProcessLoc, cond);
	    
            dst.ttype = TagConstants.MODIFIERPRAGMA;
        } else if (inProcessTag == TagConstants.LOOP_PREDICATE) {
            dst.startingLoc = inProcessLoc;
            Expr e = parseExpression(scanner);
            dst.auxVal = ExprStmtPragma.make(inProcessTag, e, inProcessLoc);
            dst.ttype = TagConstants.STMTPRAGMA;
        } else if (inProcessTag == TagConstants.JML_DEPENDS) {
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
     * expression is an expression of the form
     * <pre>
     * \result
     * \lockset
     * (*...*)
     * Function '('
     * '\type' '('
     * '(' {'\forall'|'\exists'} Type
     * '(' {'\lblpos'|'\lblneg'} Idn
     * </pre>
     *
     * @param l the lexer from which to read and parse.
     * @return the parsed expression.
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

            case TagConstants.RES: 
                { 
                    primary = ResExpr.make(l.startingLoc);
                    l.getNextToken();
                    break;
                }

            case TagConstants.LS: 
                { 
                    primary = LockSetExpr.make(l.startingLoc);
                    l.getNextToken();
                    break;
                }

            case TagConstants.INFORMALPRED_TOKEN:
                {
                    primary = LiteralExpr.make(TagConstants.BOOLEANLIT,
                                               new Boolean(true), l.startingLoc);
                    informalPredicateDecoration.set(primary, l.auxVal);
                    l.getNextToken();
                    break;
                }

            case TagConstants.IDENT: 
                { 
                    // First comes a Name...
                    int loc = l.startingLoc;
                    Name n = parseName(l);

                    // May be followed by ( ArgumentListopt ) :
                    if (l.ttype == TagConstants.LPAREN) {
                        int locOpenParen = l.startingLoc;
                        //l.getNextToken();

                        Identifier kw = n.identifierAt(0);
                        int tag = TagConstants.fromIdentifier(kw);

                        if (n.size()!=1) {
			    ExprVec args = parseArgumentList(l);
			    primary = AmbiguousMethodInvocation.make(n, 
					null, locOpenParen, args);

                            //fail(loc, "Annotations may not contain method calls");
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
                                primary = NaryExpr.make(loc, l.startingLoc, tag, null,  args);
                                break;
                                }
	    
                            case TagConstants.FRESH: 
                            case TagConstants.ELEMSNONNULL:
                            case TagConstants.ELEMTYPE:
                            case TagConstants.MAX: 
                            case TagConstants.PRE:
                            case TagConstants.TYPEOF: {
                       		l.getNextToken();
                                ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                primary = NaryExpr.make(loc, l.startingLoc, tag, null,  args);
                                break;
                            }
	    
                            default:
				// parseArgumentList requires that the scanner (l) must
				// be at the LPAREN, so we can't 'get' the LPAREN token
			        ExprVec args = parseArgumentList(l);
			        primary = AmbiguousMethodInvocation.make(n, 
					null, locOpenParen, args);
                            //    ErrorSet.fatal(loc, "Unknown ESC function symbol " + kw);
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
                    while ( l.lookahead(i) == TagConstants.LSQBRACKET &&
                            l.lookahead(i+1) == TagConstants.RSQBRACKET )
                        i += 2;
                    if (l.lookahead(i) == TagConstants.FIELD &&
                        l.lookahead(i+1) == TagConstants.CLASS) {
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
     * given the prefix primary expression <code>primary</code>.  A
     * primary expression suffice is an expression of the form
     *
     * @param l the lexer from which to read and parse.
     * @param primary the primary expression previously parsed.
     * @return the parsed expression.
     */
    protected Expr parsePrimarySuffix(Lex l, Expr primary) {
        for(;;) {
            primary = super.parsePrimarySuffix(l, primary);

            if( l.ttype == TagConstants.LSQBRACKET 
                && l.lookahead(1) == TagConstants.STAR 
                &&  l.lookahead(2) == TagConstants.RSQBRACKET) 
            {
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
    //@ requires tag == TagConstants.FORALL || tag == TagConstants.EXISTS;
    //@ ensures \result != null;
    private QuantifiedExpr 
            parseQuantifierRemainder(Lex /*@ non_null @*/ l,
                                     int tag,
                                     Type /*@ non_null @*/ type,
                                     int loc) {
        int idLoc = l.startingLoc;
        Identifier idn = parseIdentifier(l);
        LocalVarDecl v = LocalVarDecl.make(0, null, idn, type, idLoc,
                                           null, Location.NULL);

        GenericVarDeclVec vs = GenericVarDeclVec.make();
        vs.addElement(v);
    
        int endLoc = 0 /*@ uninitialized @*/;
        Expr rest = null /*@ uninitialized @*/;
        if (l.ttype == TagConstants.COMMA) {
            l.getNextToken();
            QuantifiedExpr r = parseQuantifierRemainder(l, tag, type, Location.NULL);
            rest = r;
            endLoc = r.eloc;
        } else if (l.ttype == TagConstants.SEMICOLON) {
            l.getNextToken();
            boolean emptyRange = false;
            if (l.ttype == TagConstants.SEMICOLON) {
                l.getNextToken();  // eat the semicolon
                emptyRange = true;
            }
            rest = parseExpression(l);
            if (!emptyRange && l.ttype == TagConstants.SEMICOLON) {
                // there is a nonempty range expression
                int locSemi = l.startingLoc;
                l.getNextToken();  // eat the semicolon
                Expr term = parseExpression(l);
                if (tag == TagConstants.FORALL) {
                    rest = BinaryExpr.make(TagConstants.IMPLIES, rest, term, locSemi);
                } else {
                    rest = BinaryExpr.make(TagConstants.AND, rest, term, locSemi);
                }
            }
            endLoc = l.startingLoc;
            expect(l, TagConstants.RPAREN);
        } else
            ErrorSet.fatal(l.startingLoc, "Syntax error in quantified expression.");
        return QuantifiedExpr.make(loc, endLoc, tag, vs, rest, null);
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
            parseExsuresFormalParaDecl(EscPragmaLex /*@ non_null @*/ l) {
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
    //@ ensures \result != null;
    //@ ensures \result.syntax;
    public Type parseExsuresType(EscPragmaLex /*@ non_null @*/ l) {
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
    //@ ensures \result != null
    //@ ensures \result.syntax
    public Type parseExsuresPrimitiveTypeOrTypeName(EscPragmaLex /*@ non_null @*/ l) {
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
    public PrimitiveType parseExsuresPrimitiveType(EscPragmaLex /*@ non_null @*/ l) {
	int tag;
	switch(l.ttype) {
            case TagConstants.TYPETYPE:tag = TagConstants.TYPECODE;    break;
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
    //@ ensures \result != null
    //@ ensures \result.syntax
    public TypeName parseExsuresTypeName(EscPragmaLex /*@ non_null @*/ l) {
	return parseTypeName(l);	
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
        for(;;) {
            if (l.ttype == TagConstants.MODIFIERPRAGMA) {
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
	      if (inModel) {
		  int tag = l.ttype;
		  if (tag == TagConstants.IDENT)
			    tag = TagConstants.fromIdentifier(l.identifierVal);
		  if (tag == TagConstants.JML_PURE) {
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

    public boolean isRedundant(int tag) {
	return (tag == TagConstants.JML_REQUIRES_REDUNDANTLY) ||
	     (tag == TagConstants.JML_ENSURES_REDUNDANTLY) ||
	     (tag == TagConstants.JML_PRE_REDUNDANTLY) ||
	     (tag == TagConstants.JML_DIVERGES_REDUNDANTLY) ||
	     (tag == TagConstants.JML_WHEN_REDUNDANTLY) ||
	     (tag == TagConstants.JML_POST_REDUNDANTLY) ||
	     (tag == TagConstants.JML_EXSURES_REDUNDANTLY) ||
	     (tag == TagConstants.JML_SIGNALS_REDUNDANTLY) ||
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
}
