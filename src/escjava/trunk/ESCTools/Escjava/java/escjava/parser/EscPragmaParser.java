/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.parser;

import javafe.ast.*;
import escjava.ast.*;
import escjava.ast.TagConstants;

import javafe.parser.Lex;
import javafe.parser.PragmaParser;
import javafe.parser.Token;
import javafe.parser.Parse;
import javafe.util.Location;
import javafe.util.CorrelatedReader;
import javafe.util.ErrorSet;
import javafe.util.Assert;

import escjava.Main;

import java.io.IOException;

/**
 Grammar:

 <pre>
 Pragma ::= LexicalPragma | ModifierPragma | TypeDeclElemPragma | StmtPragma

 LexicalPragma ::= "nowarn" [ Idn [',' Idn]* ] [';']


 StmtPragma ::= SimpleStmtPragma [';']
 | ExprStmtPragma SpecExpr [';']
 | 'set' PrimaryExpr '=' SpecExpr [';']

 SimpleStmtPragma ::= 'unreachable'

 ExprStmtPragma ::= 'assume' | 'assert' | 'loop_invariant' | 'decreases'
 | 'loop_predicate' | JmlExprStmtPragma

 JmlExprStmtPragma ::= 'maintaining' | 'loop_inv' | 'decreasing'

 TypeDeclElemPragma ::=
 ExprDeclPragma SpecExpr [';']
 | 'ghost' Modifiers Type VariableDeclarator [';']
 | 'still_deferred' Idn [',' Idn]* [';']

 ExprDeclPragma ::= 'axiom' | 'invariant'


 ModifierPragma ::=
 SimpleModifierPragma 
 | ExprModifierPragma SpecExpr [';']
 | VarExprModifierPragma '(' Type Idn ')' SpecExpr [';']
 | 'monitored_by' SpecExpr [',' SpecExpr]* [';']
 | ModifiesModifierPragma SpecDesignator [',' SpecDesignator]* [';']

 SimpleModifierPragma ::=
 'uninitialized' | 'monitored' | 'non_null' | 'spec_public'
 | 'writable_deferred' | 'helper' | JmlModifierPragma

 JmlModifierPragma ::=
 'public' | 'private' | 'protected' | 'spec_protected' | 'model' |
 'pure' | 'instance' | 'transient'

 ExprModifierPragma ::= 'readable_if' | 'writable_if' | 'requires'
 | 'also_requires' (if Main.allowAlsoRequires)
 | 'ensures' | 'also_ensures' | JmlExprModifierPragma

 JmlExprModifierPragma ::= 'also' | 'pre' | 'post'

 VarExprModifierPragma ::= 'exsures' | 'also_exsures" 
 | JmlVarExprModifierPragma

 JmlVarExprModifierPragma ::= 'signals' | 'also'

 ModifiesModifierPragma ::= 'modifies' | 'also_modifies' 
 | JmlModifiesModifierPragma

 JmlModifiesModifierPragma ::= 'assignable' | 'modifiable'
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

 * Also, the grammar for Type is extended (recursively) with the new base
 * type 'TYPE'.
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
 */

public class EscPragmaParser extends Parse implements PragmaParser
{
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

    /** 
     * The value -2 means there is nothing else to process.  The value
     * -1 means there is something to process and the next thing to
     * read begins a new pragma (or ends the pragma-containing
     * comment).  The other values indicate that the pragma parser is
     * in the middle of parsing some pragma, and is expected to
     * continue this parsing next time it gets control.
     */
    private int inProcessTag;
    /*@ invariant inProcessTag == -2 || inProcessTag == -1 ||
      @           inProcessTag==TagConstants.STILL_DEFERRED ||
      @           inProcessTag==TagConstants.MONITORED_BY ||
      @           inProcessTag==TagConstants.MODIFIES ||
      @           inProcessTag==TagConstants.ALSO_MODIFIES ||
      @           inProcessTag==TagConstants.JML_MODIFIABLE ||
      @           inProcessTag==TagConstants.JML_ASSIGNABLE ||
      @           inProcessTag==TagConstants.LOOP_PREDICATE ||
      @           inProcessTag==TagConstants.JML_ALSO; 
      @*/

    private int inProcessLoc;
    private CorrelatedReader pendingJavadocComment;

    /**
     * Indicates that we have parsed an "also" JML keyword and thus
     * all following REQUIRES, ENSURES, EXSURES, and MODIFIES should
     * be parsed as ALSO_REQUIRES, ALSO_ENSURES, ALSO_EXSURES, and
     * ALSO_MODIFIES.  This flag should be cleared when we have
     * finished parsing the current method specification.
     */
    private boolean inAlsoClause = false;

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
	addOperator(TagConstants.IMPLIES, 76, false);
	addOperator(TagConstants.EXPLIES, 76, true);
	addOperator(TagConstants.IFF, 73, true);
	addOperator(TagConstants.NIFF, 73, true);
	addOperator(TagConstants.SUBTYPE, 140, true);
	scanner.addKeyword("\\result", TagConstants.RES);
	scanner.addKeyword("\\lockset", TagConstants.LS);
	scanner.addKeyword("\\TYPE", TagConstants.TYPETYPE);
	inProcessTag = -2;
        inAlsoClause = false;
    }

    /**
     * @param tag the comment tag character to check.
     * @return true iff tag is an '@' or an '*' character.
     */
    public boolean checkTag(int tag) {
        return tag == '@' || tag == '*';
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
                inProcessTag = -1;
                break;

            case '*':
                if (eolComment) {
                    // This is not a Javadoc comment, so ignore
                    inProcessTag = -2;
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
            inProcessTag = -2;
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
            inProcessTag = -1;
            return true;
        } else {
            ErrorSet.error(startLoc,
                           "Pragma in javadoc comment is not correctly " +
                           "terminated (missing " + endEnclosedPragma + ")");
            pendingJavadocComment = null;
            inProcessTag = -2;
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
     * @param dst the token in which to store information about the
     * current pragma.
     * @return a flag indicating if further pragmas need to be parsed.
     * @see Lex
     */
    public boolean getNextPragma(Token /*@ non_null @*/ dst) {
        try {
            if (inProcessTag == -2) {
                return false;
            }

            // See if we need to continue a previous pragma, for example
            // "monitored_by", which can take multiple SpecExprs
            if (inProcessTag != -1) { continuePragma(dst); return true; }

            if (scanner.ttype == TagConstants.EOF) { 
                LexicalPragma PP = scanner.popLexicalPragma();
                if (PP!=null) {
                    dst.ttype = TagConstants.LEXICALPRAGMA;
                    dst.auxVal = PP;
                    return true;
                }

                if (pendingJavadocComment != null) {
                    scanner.close();
                    if (processJavadocComment()) {
                        return true;
                    }
                }
                close();
                return false;
            }
            //@ assume scanner.m_in != null;  // TBW: is this right??  --KRML

            // Start a new pragma
            int loc = scanner.startingLoc;
            if (scanner.ttype != TagConstants.IDENT)
                ErrorSet.fatal(loc, "Pragma must start with an identifier");
            Identifier kw = scanner.identifierVal;
            scanner.getNextToken();

            int tag = TagConstants.fromIdentifier(kw);
            boolean semiNotOptional = false;

            switch (tag) {
                
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
                if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
                if (scanner.ttype != TagConstants.EOF)
                    ErrorSet.fatal(loc, "Syntax error in nowarn pragma");
                    break;

                case TagConstants.STILL_DEFERRED:
                case TagConstants.MONITORED_BY:
                case TagConstants.MODIFIES:
                case TagConstants.ALSO_MODIFIES:
                case TagConstants.JML_MODIFIABLE:
                case TagConstants.JML_ASSIGNABLE:
                    if (tag == TagConstants.JML_MODIFIABLE 
                        || tag == TagConstants.JML_ASSIGNABLE) {
                        ErrorSet.caution(loc, "ESC/Java keyword 'modifies' " +
                                         "is preferred to JML keywords " + 
                                         "'modifiable' and 'assignable'.");
                    }
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    return true;

                case TagConstants.UNREACHABLE:
                    dst.ttype = TagConstants.STMTPRAGMA;
                    dst.auxVal = SimpleStmtPragma.make(tag, loc);
                    if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
                    break;
	
                case TagConstants.ASSERT:
                case TagConstants.ASSUME:
                case TagConstants.LOOP_INVARIANT:
                case TagConstants.JML_MAINTAINING:
                case TagConstants.DECREASES:
                case TagConstants.JML_DECREASING:
                    if (tag == TagConstants.JML_MAINTAINING 
                        || tag == TagConstants.JML_DECREASING) {
                        ErrorSet.caution(loc, "ESC/Java keywords 'loop_invariant' and " +
                                         "'decreases' are preferred to JML keywords " + 
                                         "'maintaining' and 'decreasing'.");
                    }
                    dst.ttype = TagConstants.STMTPRAGMA;
                    dst.auxVal = ExprStmtPragma.make(tag, parseExpression(scanner), loc);
                    semiNotOptional = true;
                    break;

                case TagConstants.LOOP_PREDICATE:
                    inProcessTag = tag;
                    inProcessLoc = loc;
                    continuePragma(dst);
                    semiNotOptional = true;
                    return true;	  

                case TagConstants.SET:
                    dst.ttype = TagConstants.STMTPRAGMA;
                    Expr target = parsePrimaryExpression(scanner);
                    int locOp = scanner.startingLoc;
                    expect(scanner, TagConstants.ASSIGN);
                    Expr value = parseExpression(scanner);
                    dst.auxVal = SetStmtPragma.make(target, locOp, value, loc);
                    semiNotOptional = true;
                    break;

                case TagConstants.AXIOM:
                case TagConstants.INVARIANT:
                    dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
                    dst.auxVal = ExprDeclPragma.make(tag, parseExpression(scanner), loc);
                    semiNotOptional = true;
                    break;

                case TagConstants.GHOST:
                    {
                        dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
	      
                        int modifiers = parseModifiers(scanner);
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
                                 "Only one ghost field may be declared per ghost annotation.");
	      
                        dst.auxVal = GhostDeclPragma.make(decl, loc);
                        semiNotOptional = true;
                        break;
                    }

                case TagConstants.SKOLEM_CONSTANT:
                    {
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
                case TagConstants.SPEC_PUBLIC:
                case TagConstants.WRITABLE_DEFERRED:
                case TagConstants.HELPER:
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal = SimpleModifierPragma.make(tag, loc);
                    break;

                case TagConstants.DEFINED_IF:
                case TagConstants.WRITABLE_IF:
                case TagConstants.REQUIRES:
                case TagConstants.ALSO_REQUIRES:
                case TagConstants.ENSURES:
                case TagConstants.ALSO_ENSURES:
                case TagConstants.JML_PRE:
                case TagConstants.JML_POST:
                    if ((tag == TagConstants.ALSO_REQUIRES ||
                        (tag == TagConstants.REQUIRES && inAlsoClause))
                        && !Main.allowAlsoRequires)
                        ErrorSet.fatal(loc, TagConstants.toString(tag) +
                                       " is not allowed pragma");
                    if (tag == TagConstants.JML_POST || tag == TagConstants.JML_PRE)
                        ErrorSet.caution(loc, "ESC/Java keywords 'require' and 'ensures' " +
                                         "are preferred to JML keywords " + 
                                         "'pre' and 'post'.");
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    dst.auxVal
                        = ExprModifierPragma.make(tag, parseExpression(scanner), loc);
                    semiNotOptional = true;
                    break;

                case TagConstants.JML_ALSO:
                    if (inAlsoClause)
                        ErrorSet.warning(loc, "Already in an 'also' specification; " + 
                                         "duplicate 'also' ignored.");
                    inAlsoClause = true;
                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    semiNotOptional = true;
                    return true;

                case TagConstants.EXSURES:
                case TagConstants.ALSO_EXSURES:
                case TagConstants.JML_SIGNALS: {
                    if (tag == TagConstants.JML_SIGNALS) {
                        ErrorSet.caution(loc, "ESC/Java keywords 'exsures' " +
                                         "is preferred to JML keyword " + 
                                         "'signals'.");
                    }

                    dst.ttype = TagConstants.MODIFIERPRAGMA;
                    expect(scanner, TagConstants.LPAREN);
                    FormalParaDecl arg = parseExsuresFormalParaDecl(scanner);
                    expect(scanner, TagConstants.RPAREN);
                    Expr expr = parseExpression(scanner);
                    dst.auxVal
                        = VarExprModifierPragma.make(tag, arg, expr, loc);
                    semiNotOptional = true;
                    break;
                }
	
                default:
                    ErrorSet.fatal(loc, "Unrecognized pragma");
            }

            if (semiNotOptional)
                if (scanner.ttype == TagConstants.SEMICOLON) scanner.getNextToken();
                else if (scanner.ttype != TagConstants.EOF)
                    ErrorSet.fatal(scanner.startingLoc, 
                                   ("Semicolon required when a " + kw.toString()
                                    + " pragma is followed by another pragma."));

            return true;
        } catch (IOException e) { return false; }
    }

    /*@ requires inProcessTag==TagConstants.STILL_DEFERRED ||
      @          inProcessTag==TagConstants.MONITORED_BY ||
      @          inProcessTag==TagConstants.MODIFIES ||
      @          inProcessTag==TagConstants.ALSO_MODIFIES ||
      @          inProcessTag==TagConstants.JML_MODIFIABLE ||
      @          inProcessTag==TagConstants.JML_ASSIGNABLE ||
      @          inProcessTag==TagConstants.LOOP_PREDICATE */
    //@ requires scanner.startingLoc != Location.NULL;
    //@ requires scanner.m_in != null;
    private void continuePragma(Token /*@ non_null @*/ dst) throws IOException {
        if (inProcessTag == TagConstants.STILL_DEFERRED) {
            int locId = scanner.startingLoc;
            Identifier idn = parseIdentifier(scanner);
            dst.ttype = TagConstants.TYPEDECLELEMPRAGMA;
            dst.auxVal = StillDeferredDeclPragma.make(idn, inProcessLoc, locId);
        } else if (inProcessTag == TagConstants.MONITORED_BY
                   || inProcessTag == TagConstants.MODIFIES
                   || inProcessTag == TagConstants.ALSO_MODIFIES
                   || inProcessTag == TagConstants.JML_MODIFIABLE
                   || inProcessTag == TagConstants.JML_ASSIGNABLE) {
            dst.startingLoc = inProcessLoc;
            Expr e = parseExpression(scanner);
            dst.auxVal = ExprModifierPragma.make(inProcessTag, e, inProcessLoc);
            dst.ttype = TagConstants.MODIFIERPRAGMA;
        } else if (inProcessTag == TagConstants.LOOP_PREDICATE) {
            dst.startingLoc = inProcessLoc;
            Expr e = parseExpression(scanner);
            dst.auxVal = ExprStmtPragma.make(inProcessTag, e, inProcessLoc);
            dst.ttype = TagConstants.STMTPRAGMA;
        } else Assert.precondition(false);

        switch (scanner.ttype) {
            case TagConstants.SEMICOLON:
                scanner.getNextToken();
            case TagConstants.EOF:
                inProcessTag = -1;
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
                        l.getNextToken();

                        Identifier kw = n.identifierAt(0);
                        int tag = TagConstants.fromIdentifier(kw);

                        if (n.size()!=1)
                            fail(loc, "Annotations may not contain method calls");
                        switch (tag) {
                            case TagConstants.TYPE:
                                {
                                    Type subexpr = parseType(l);
                                    primary = TypeExpr.make(loc, l.startingLoc, subexpr);
                                    expect(l, TagConstants.RPAREN);
                                    break;
                                }
	    
                            case TagConstants.DTTFSA:
                                {
                                    Type t = parseType(l);
                                    TypeExpr te = TypeExpr.make(loc, l.startingLoc, t);
                                    expect(l, TagConstants.COMMA);
                                    ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                    args.insertElementAt(te, 0);
                                    primary = NaryExpr.make(loc, l.startingLoc, tag, args);
                                    break;
                                }
	    
                            case TagConstants.FRESH: 
                            case TagConstants.ELEMSNONNULL:
                            case TagConstants.ELEMTYPE:
                            case TagConstants.MAX: 
                            case TagConstants.PRE:
                            case TagConstants.TYPEOF:
                                {
                                    ExprVec args = parseExpressionList(l, TagConstants.RPAREN);
                                    primary = NaryExpr.make(loc, l.startingLoc, tag, args);
                                    break;
                                }
	    
                            default:
                                ErrorSet.fatal(loc, "Unknown ESC function symbol " + kw);
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
}
