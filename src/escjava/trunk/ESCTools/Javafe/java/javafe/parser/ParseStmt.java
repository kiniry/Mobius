/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser;

import javafe.ast.*;
import javafe.util.StackVector;
import javafe.util.Location;
import javafe.util.Assert;
import javafe.Tool;

/**
 * <code>Parse</code> objects parse Java statements, creating AST
 * structures for the parsed input using the static
 * <code>make*()</code> methods of the classes in the
 * <code>javafe.ast</code> package.
 *
 * <p> The concrete grammar for statements is as follows:
 * <pre>
 * Statement:
 * ';'
 * | (Modifier | ModifierPragma)* ClassDeclaration
 * | (Modifier | ModifierPragma)* Type { Idn [ '=' InitExpr ] },+ ';'
 * | Idn ':' Stmt
 * | Expr ';'
 * | '{' BlockStmt* '}'
 * // In an assert, BoolExpr must be of type boolean, NonVoidExpr must 
 * // not be of type void
 * | 'assert' BoolExpr [ ':' NonVoidExpr ] ';'
 * | 'break' [ Idn ] ';'
 * | 'continue' [ Idn ] ';'
 * | 'return' [ Expr ] ';'
 * | 'throw' Expr ';'
 * | 'if' '(' Expr ')' Stmt [ 'else' Stmt ]
 * | 'do' Stmt 'while' '(' Expr ')' ';'
 * | 'while' '(' Expr ')' Stmt
 * | 'for' '(' [ VDeclInit | StmtExpr,* ] ';' Expr ';' StmtExpr,* ')' Stmt
 * | 'switch' '(' Expr ')'
 *     '{' { {'case' Expr ':' | 'default:'}* BlockStmt* }* '}'
 * | 'synchronized' '(' Expr ')' '{' BlockStmt* '}'
 * | 'try' '{' BlockStmt* '}' { 'catch' '(' VDecl,* ')' '{' BlockStmt* '}' }*
 *     [ 'finally' '{' BlockStmt* '}' ]
 * | StmtPragma
 * </pre>
 * 
 * <p> Currently, there is no error recovery.  Upon detection of a
 * syntax error, all methods in this class throw a {@link
 * RuntimeException} with a (weak) error message.
 * 
 * <p> Although the class as a whole is thread-safe, that is,
 * different threads can be calling methods of different instances of
 * <code>ParseStmt</code> at the same time, individual instances are
 * not.
 * 
 * @see javafe.ast.ASTNode
 */

public abstract class ParseStmt extends ParseExpr
{
    public ParseStmt() {
	//@ set seqStmt.elementType = \type(Stmt)
	//@ set seqStmt.owner = this

	//@ set seqCatchClause.elementType = \type(CatchClause)
	//@ set seqCatchClause.owner = this
    }

    /**
     * Internal working storage for many <code>ParseStmt</code>
     * functions.
     */
    //@ invariant seqStmt.elementType == \type(Stmt)
    //@ invariant seqStmt.owner == this
    protected final /*@non_null*/ StackVector seqStmt
            = new StackVector();

    //* Internal working storage for parseCatches function.
    //@ invariant seqCatchClause.elementType == \type(CatchClause)
    //@ invariant seqCatchClause.owner == this
    protected final /*@non_null*/ StackVector seqCatchClause
            = new StackVector();

    /**
     * Parse a type declaration stating at the class/interface
     * keyword.  A declaration of this method is needed because class
     * declarations can be in statements.  However, the body (and more
     * documentation) lives in Parse.java.
     */
    //@ requires l != null && l.m_in != null
    //@ requires loc != Location.NULL
    //@ modifies l.ttype
    //@ ensures \result != null
    //@ ensures \old(l.ttype)==TagConstants.CLASS ==> \result instanceof ClassDecl
    abstract TypeDecl parseTypeDeclTail(Lex l, boolean specOnly, int loc, 
                                        int modifiers,
                                        ModifierPragmaVec modifierPragmas);
  
    /**
     * Method for parsing a <code>Stmt</code>.
     *
     * <p> Effects: Parses a single <code>Stmt</code> according to the
     * grammar at the top of this file, <em>except</em> that it does
     * not accept variable-declaration statements.  If no syntax
     * errors are encountered, it adds one or more <code>Stmt</code>
     * to <code>seqStmt</code>, leaving <code>l</code> at the token
     * just after the trailing <code>}</code> of the statement.  More
     * than one statement is added only in the case of variable
     * declarations that declare more than one variable.
     */
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    public Stmt parseStatement(Lex l) {
        if (l.ttype == TagConstants.LBRACE) // As an optimization, handle specially
            return parseBlock(l, false);
        else {
            seqStmt.push();
            int loc = l.startingLoc;
            addStmt(l);
            Stmt result = (Stmt)seqStmt.elementAt(0);
            if (seqStmt.size() != 1 || result instanceof VarDeclStmt) {
                fail(loc,
                     "Variable declarations are not legal in this context.");
            }
            if (result instanceof StmtPragma) {
                fail(loc,
                     "Statement pragmas are not legal in this context.");
            }

            seqStmt.pop();
            return result;
        }
    }

    /**
     * Internal method for parsing a <code>Stmt</code>.
     *
     * <p> Effects: Parses a single <code>Stmt</code> according to the
     * grammar at the top of this file.  If no syntax errors are
     * encountered, it adds one or more <code>Stmt</code> to
     * <code>seqStmt</code>, leaving <code>l</code> at the token just
     * after the trailing <code>}</code> of the statement.  More than
     * one statement is added only in the case of variable
     * declarations that declare more than one variable.
     */
    //@ requires l != null && l.m_in != null
    //@ modifies seqStmt.elementCount, seqStmt.currentStackBottom
    /*@ ensures (seqStmt.elementCount - seqStmt.currentStackBottom) >
     (\old(seqStmt.elementCount) - \old(seqStmt.currentStackBottom)) @*/
    private void addStmt(Lex l) {
        int ttype = l.ttype;

        // Stmt ::= ';'
        if (ttype == TagConstants.SEMICOLON) {
            int loc = l.startingLoc;
            l.getNextToken(); // Discard ';'
            seqStmt.addElement( SkipStmt.make(loc) );
            return;
        }

        // Stmt ::= Idn ':' Stmt
        //          | Idn { '[' ']' }* { Idn ['=' InitExpr] },+
        //          | Expr ';'
        if (ttype == TagConstants.IDENT) {
            //@ assert (!l.toString().equals("assert")));
            Expr e = parseExpression(l);
            if (e.getTag() == TagConstants.AMBIGUOUSVARIABLEACCESS) {
                Name n = ((AmbiguousVariableAccess)e).name;

                // Check to see if we have a labeled expr...
                if (l.ttype == TagConstants.COLON) {
                    l.getNextToken(); // Discard ':'
                    if (n.size() != 1)
                        fail(l.startingLoc, "Can't have qualified name in this context");
                    Identifier id = n.identifierAt(0);
                    int locId = n.locIdAt(0);
                    seqStmt.addElement( LabelStmt.make(id, parseStatement(l), locId) );
                    return;
                }

                // Assume we have a variable declaration
                // first, look for modifiers on type name
                TypeModifierPragmaVec tmodifiers = null;
                tmodifiers = parseTypeModifierPragmas(l);
                Type basetype = TypeName.make(tmodifiers, n);

                basetype = parseBracketPairs(l, basetype);
                addVarDeclStmts(l, Modifiers.NONE, null, basetype);
                expect(l, TagConstants.SEMICOLON);
                return;
            } else {
                expect(l, TagConstants.SEMICOLON);
                // TODO: make sure e is a statement expr
                seqStmt.addElement( EvalStmt.make(e) );
                return;
            }
        }

        // Stmt ::= '{' ... '}'  (that is, a Block)
        if (ttype == TagConstants.LBRACE) {
            seqStmt.addElement( parseBlock(l, false) );
            return;
        }
     
        // Stmt ::= <keyword> ...
        int keywordloc = l.startingLoc;
        switch (ttype) {
            case TagConstants.ASSERT: { // 'assert' BoolExpr [ ':' NonVoidExpr ] ';'
                // Only process if we are supposed to be parsing Java
                // 1.4 or later.
                if (!Tool.options.assertIsKeyword) {
                    fail(l.startingLoc, "Java keyword \"assert\" is only supported if the" +
                         "-source 1.4 option is provided.");
                }
                
                l.getNextToken(); // Discard the keyword
                Expr predicate = parseExpression(l);
                Expr label = null;
                if (l.ttype == TagConstants.COLON) {
                    l.getNextToken();
                    label = parseExpression(l);
                }
                expect(l, TagConstants.SEMICOLON);
                seqStmt.addElement(AssertStmt.make(predicate, label, keywordloc));
                return;
            }
      
            case TagConstants.BREAK: // 'break' [ Idn ] ';'
            case TagConstants.CONTINUE: { // 'continue' [ Idn ] ';'
                l.getNextToken(); // Discard the keyword
                Identifier label = null;
                if (l.ttype == TagConstants.IDENT) {
                    label = l.identifierVal;
                    l.getNextToken(); // Discard IDENT
                }
                expect(l, TagConstants.SEMICOLON);
                seqStmt.addElement(ttype == TagConstants.BREAK ?
                                   (Stmt)BreakStmt.make(label, keywordloc)
                                   : (Stmt)ContinueStmt.make(label, keywordloc));
                return;
            }
				
            case TagConstants.RETURN: // 'return' Expr ';'
                l.getNextToken(); // Discard the keyword
                if (l.ttype == TagConstants.SEMICOLON) {
                    l.getNextToken(); // Discard ';'
                    seqStmt.addElement( ReturnStmt.make(null, keywordloc) );
                } else {
                    Expr expr = parseExpression(l);
                    expect(l, TagConstants.SEMICOLON);
                    seqStmt.addElement(ReturnStmt.make(expr, keywordloc));
                }
                return;
				
            case TagConstants.THROW: { // 'throw' Expr ';'
                l.getNextToken(); // Discard the keyword
                Expr expr = parseExpression(l);
                expect(l, TagConstants.SEMICOLON);
                seqStmt.addElement(ThrowStmt.make(expr, keywordloc));
                return;
            }

            case TagConstants.IF: { // 'if' '(' Expr ')' Stmt [ 'else' Stmt ]
                l.getNextToken(); // Discard the keyword
                expect(l, TagConstants.LPAREN);
                Expr test = parseExpression(l);
                expect(l, TagConstants.RPAREN);
                Stmt consequence = parseStatement(l);
                Stmt alternative;
                if (l.ttype == TagConstants.ELSE) {
                    l.getNextToken(); // Discard 'else'
                    alternative = parseStatement(l);
                } else
                    // set the location of the implicit Skip to be that of the If
                    alternative = SkipStmt.make(keywordloc);
                seqStmt.addElement(IfStmt.make(test, consequence, alternative,
                                               keywordloc));
                return;
            }

            case TagConstants.DO: { // 'do' Stmt 'while' '(' Expr ')' ';'
                l.getNextToken(); // Discard the keyword
                Stmt body = parseStatement(l);
                expect(l, TagConstants.WHILE);
                expect(l, TagConstants.LPAREN);
                Expr test = parseExpression(l);
                expect(l, TagConstants.RPAREN);
                expect(l, TagConstants.SEMICOLON);
                seqStmt.addElement( DoStmt.make(test, body, keywordloc) );
                return;
            }

            case TagConstants.WHILE: { // 'while' '(' Expr ')' Stmt
                l.getNextToken(); // Discard the keyword
                int locGuardOpenParen = l.startingLoc;
                expect(l, TagConstants.LPAREN);
                Expr test = parseExpression(l);
                expect(l, TagConstants.RPAREN);
                Stmt body = parseStatement(l);
                seqStmt.addElement( WhileStmt.make(test, body, keywordloc,
                                                   locGuardOpenParen) );
                return;
            }
		 
            case TagConstants.FOR: {
                l.getNextToken(); // Discard the keyword
                seqStmt.addElement( parseForStmt(l, keywordloc) );
                return;
            }

            case TagConstants.SWITCH: {
                l.getNextToken(); // Discard the keyword
                seqStmt.addElement( parseSwitchStmt(l, keywordloc) );
                return;
            }

            case TagConstants.SYNCHRONIZED: { // 'synchronized' '(' Expr ')' '{' BlockStmt* '}'
                l.getNextToken(); // Discard the keyword
                int locOpenParen = l.startingLoc;
                expect(l, TagConstants.LPAREN);
                Expr value = parseExpression(l);
                expect(l, TagConstants.RPAREN);
                BlockStmt body = parseBlock(l, false);
                seqStmt.addElement( SynchronizeStmt.make(value, body, keywordloc,
                                                         locOpenParen));
                return;
            }
      
            case TagConstants.TRY: { //'try' '{' BlockStmt* '}' Catches ['finally' '{'BlockStmt*'}']
                l.getNextToken(); // Discard the keyword
                int openloc = l.startingLoc;
                Stmt body = parseBlock(l, false);

                CatchClauseVec catches = parseCatches(l);

                if (l.ttype == TagConstants.FINALLY) {
                    int finloc = l.startingLoc;
                    l.getNextToken(); // Discard 'finally'
                    Stmt fbody = parseBlock(l, false);
                    if (catches != null) {
                        Stmt s = TryCatchStmt.make(body, catches, keywordloc);
                        seqStmt.addElement( TryFinallyStmt.make(s, fbody, keywordloc,
                                                                finloc) );
                    } else seqStmt.addElement( TryFinallyStmt.make(body, fbody,
                                                                   keywordloc, finloc) );
                    return;
                } else {
                    if (catches == null) 
                        fail(l.startingLoc, "Missing handlers in try statement");
                    seqStmt.addElement( TryCatchStmt.make(body, catches, keywordloc) );
                    return;
                }
            }
        }

        // Stmt ::= ClassDecl | VarDeclInit   (Except those starting with IDENT)
        {
            int modifiers = parseModifiers(l);
            ModifierPragmaVec pmodifiers = this.modifierPragmas;

            if (l.ttype == TagConstants.CLASS) {
                ClassDecl cd = (ClassDecl)parseTypeDeclTail(l, false, keywordloc,
                                                            modifiers, pmodifiers);
                seqStmt.addElement(ClassDeclStmt.make(cd));
                return;
            } else if (modifiers != Modifiers.NONE || pmodifiers != null ||
                       isPrimitiveKeywordTag(ttype)) {
                addVarDeclStmts(l, modifiers, pmodifiers, parseType(l));
                expect(l, TagConstants.SEMICOLON);
                return;
            }
        }

        // Check for StmtPragma
        if( ttype == TagConstants.STMTPRAGMA ) {
            StmtPragma pragma = (StmtPragma)l.auxVal;
            seqStmt.addElement( (Stmt)pragma );
            l.getNextToken();
            return;
        }

        // Assume it's a statement expression...
        Expr e = parseExpression(l);
        if (! isStatementExpression(e)) 
            fail(l.startingLoc, "Statement expression expected");
        seqStmt.addElement( EvalStmt.make(e) );
        expect(l, TagConstants.SEMICOLON);
        return;
    }

    /**
     * Method for parsing a <code>ConstructorBody</code>.
     *
     * <p> Effects: Parses the following grammar:
     * <pre>
     * Block ::=
     * '{' [ { 'this' | 'super' ] '(' ArgumentList ')' ] { VarDeclInit | Stmt }* '}'
     * </pre>
     *
     * <p> If no syntax errors are encountered, it returns a parse
     * tree for the parsed input, leaving <code>l</code> at the token
     * just after the trailing <code>}</code> of the statement.
     */
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    public BlockStmt parseConstructorBody(Lex l) {
        int openloc = l.startingLoc;
        expect(l, TagConstants.LBRACE);
        seqStmt.push();

        // Handle leading constructor invocation; 
        // make one up if missing and the class being declared in not object

        if (((l.ttype == TagConstants.THIS || l.ttype == TagConstants.SUPER)
             && l.lookahead(1) == TagConstants.LPAREN)) {
            boolean superCall = (l.ttype == TagConstants.SUPER);
            int loc = l.startingLoc;
            l.getNextToken();
            // Next, parse the argument list, which should start with an open
            // parenthesis.  As a check that "parseArgumentList" doesn't accept
            // any other first token than an open parenthesis, the tag of the next
            // token is stored in "tagShouldBeLParen", and it is assert that
            // *if* "parseArgumentList" returns normally, then the tag recorded
            // is indeed an open parenthesis.
            int locOpenParen = l.startingLoc;
            int tagShouldBeLParen = l.ttype;
            ExprVec args = parseArgumentList(l);
            expect( l, TagConstants.SEMICOLON );
            seqStmt.addElement( ConstructorInvocation.make( superCall,
                                                            null, Location.NULL,
                                                            loc, locOpenParen,
                                                            args ) );
        } else {
            // Look for Primary '.' 'super' '(' ArgumentList ')' ';'
            boolean foundDotSuper = false;
            for (int i = 0; ; i++) {
                switch (l.lookahead(i)) {
                    case TagConstants.EOF:
                        break;
                    case TagConstants.LBRACE:
                        for(int braceDepth = 1; 0 < braceDepth; i++) {
                            if (l.lookahead(i) == TagConstants.RBRACE) braceDepth--;
                        }
                        continue;
                    case TagConstants.SEMICOLON:
                    case TagConstants.RBRACE:
                        break;
                    case TagConstants.FIELD:
                        if (l.lookahead(i+1) == TagConstants.SUPER) {
                            foundDotSuper = true;
                            break;
                        } else continue;
                    default: continue;
                }
                break;
            }
            if (foundDotSuper) {
                int loc = l.startingLoc;
                Expr e = parsePrimaryExpression(l);
                int locDot = l.startingLoc;
                expect(l, TagConstants.FIELD);
                expect(l, TagConstants.SUPER);
                int locOpenParen = l.startingLoc;
                ExprVec args = parseArgumentList(l);
                expect(l, TagConstants.SEMICOLON);
                seqStmt.addElement(ConstructorInvocation.make(true, e, locDot,
                                                              loc, locOpenParen,
                                                              args));
            }
        }

        // No explicit constructor invocation.  We do not know if this
        // class is java.lang.Object, so we cannot add a constructor
        // invocation here; we will do it in type checking.
      
        // Handle rest of body
        {
            int ttype = l.ttype;
            while (ttype != TagConstants.RBRACE && ttype != TagConstants.EOF) {
                addStmt(l);
                ttype = l.ttype;
            }
            if (ttype == TagConstants.EOF) 
                fail(l.startingLoc, "End of input in block");
        }
        StmtVec body = StmtVec.popFromStackVector(seqStmt);
        int closeloc = l.startingLoc;
        l.getNextToken(); // Discard '}'
        return BlockStmt.make(body, openloc, closeloc);
    }

    /**
     * Method for parsing a <code>Block</code>.
     *
     * <p> Effects: Parses the following grammar:
     * <pre>
     * Block ::=
     * '{' { VarDeclInit | Stmt }* '}'
     * </pre>
     *
     * <p> If no syntax errors are encountered, it returns a parse
     * tree for the parsed input, leaving <code>l</code> at the token
     * just after the trailing <code>}</code> of the statement.
     */
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    public BlockStmt parseBlock(Lex l, boolean specOnly) {
        int openloc = l.startingLoc;
        expect(l, TagConstants.LBRACE);
        seqStmt.push();
        {
            int ttype = l.ttype;
            while (ttype != TagConstants.RBRACE && ttype != TagConstants.EOF) {
                if (!specOnly)
                    addStmt(l);
                else {
                    if (ttype==TagConstants.LBRACE)
                        parseBlock(l, true);
                    else
                        l.getNextToken();
                }
                ttype = l.ttype;
            }
            if (ttype == TagConstants.EOF) 
                fail(l.startingLoc, "End of input in block");
        }
        StmtVec body = StmtVec.popFromStackVector(seqStmt);
        int closeloc = l.startingLoc;
        l.getNextToken(); // Discard '}'
        return BlockStmt.make(body, openloc, closeloc);
    }

    /**
     * Internal method for parsing a switch statement.
     *
     * <p> Effects: Parses the following grammar:
     * <pre>
     * ForStmtRemainder ::=
     * '(' [VDeclInit | StmtExpr,* ] ';' Expr ';' StmtExpr,* ')' Stmt
     * </pre>
     *
     * <p> Note that it assumes the leading <code>for</code> has
     * already been parsed; <code>keywordloc</code> is the location
     * assumed for the <code>for</code> token.
     *
     * <p> If no syntax errors are encountered, it returns a parse
     * tree for the parsed input, leaving <code>l</code> at the token
     * just after the trailing <code>}</code> of the statement.
     */
    //@ requires l != null && l.m_in != null
    //@ requires keywordloc != Location.NULL
    //@ ensures \result != null
    private ForStmt parseForStmt(Lex l, int keywordloc) {
        int parenloc = l.startingLoc;
        expect(l, TagConstants.LPAREN);

        // Parse ForInit ::= [VDeclInit | StmtExpr,* ] ';'
        StmtVec forInit;
        int locFirstSemi;
        { // Parse ForInit part
            seqStmt.push();

            Type basetype = null;
            int modifiers = Modifiers.NONE;
            ModifierPragmaVec pmodifiers = null;
            switch (l.ttype) {
                case TagConstants.SEMICOLON:
                    break;

                default:
                    modifiers = parseModifiers(l);
                    pmodifiers = this.modifierPragmas;

                    if (modifiers != Modifiers.NONE || pmodifiers != null ||
                        isPrimitiveKeywordTag(l.ttype)) {
                        basetype = parseType(l);
                        break;
                    }

                    Expr e = parseExpression(l);
                    if (e.getTag() == TagConstants.AMBIGUOUSVARIABLEACCESS) {
                        // Assume a var declaration
                        // look for type modifier pragmas
                        TypeModifierPragmaVec tmodifiers = null;
                        tmodifiers = parseTypeModifierPragmas(l);
                        basetype = TypeName.make(tmodifiers, ((AmbiguousVariableAccess)e).name);
	
                        break;
                    } else {
                        for(;;) {
                            if (! isStatementExpression(e)) 
                                fail(l.startingLoc, "Statement expression expected");
                            seqStmt.addElement( EvalStmt.make(e) );
                            if (l.ttype != TagConstants.COMMA) break;
                            l.getNextToken(); // Discard the COMMA
                            e = parseExpression(l);
                        }
                    }
            }

            if (basetype != null) {
                basetype = parseBracketPairs(l, basetype);
                addVarDeclStmts(l, modifiers, pmodifiers, basetype);
            }

            locFirstSemi = l.startingLoc;
            expect(l, TagConstants.SEMICOLON);
            forInit = StmtVec.popFromStackVector(seqStmt);
        }

        // Parse <pre> Test ::= [ Expr ] ';' </pre>
        Expr test;
        if (l.ttype != TagConstants.SEMICOLON)
            test = parseExpression(l);
        else test = LiteralExpr.make(TagConstants.BOOLEANLIT, 
                                     new Boolean(true), 
                                     l.startingLoc );
        expect(l, TagConstants.SEMICOLON);

        // Parse <pre> ForUpdate ::= StmtExpr,* ')' </pre>
        ExprVec forUpdate;
        {
            seqExpr.push();

            if (l.ttype != TagConstants.RPAREN) {
                for(;;) {
                    Expr e = parseExpression(l);
                    if (! isStatementExpression(e))
                        fail(l.startingLoc, "Statement expression expected.");
                    seqExpr.addElement(e);
                    if (l.ttype != TagConstants.COMMA) break;
                    l.getNextToken(); // Discard COMMA
                }
            }
            expect(l, TagConstants.RPAREN);
            forUpdate = ExprVec.popFromStackVector(seqExpr);
        }

        Stmt body = parseStatement(l);
        return ForStmt.make(forInit, test, forUpdate, body, keywordloc,
                            locFirstSemi);
    }

    /**
     * Internal method for parsing a switch statement.
     *
     * <p> Effects: Parses the following grammar:
     * <pre>
     * SwitchStmtRemainder ::=
     * '(' Expr ')' '{' { 'case' Expr ':' | 'default ':' | Stmt }* '}'
     * </pre>
     *
     * <p> Note that it assumes the trailing <code>switch</code> has
     * already been parsed; <code>keywordLoc</code> is the location
     * assumed for the <code>switch</code> token.
     *
     * <p> If no syntax errors are encountered, it returns a parse
     * tree for the parsed input, leaving <code>l</code> at the token
     * just after the trailing <code>}</code> of the statement.
     */
    //@ requires l != null && l.m_in != null
    //@ requires keywordloc != Location.NULL
    //@ ensures \result != null
    private SwitchStmt parseSwitchStmt(Lex l, int keywordloc) {
        // Read value to be tested
        expect(l, TagConstants.LPAREN);
        Expr value = parseExpression(l);
        expect(l, TagConstants.RPAREN);

        // Read body
        int openloc = l.startingLoc;
        expect(l, TagConstants.LBRACE);
        boolean atStart=true;
        boolean hasDefault = false;
        seqStmt.push();
        while (l.ttype != TagConstants.RBRACE && l.ttype != TagConstants.EOF) {
            if (l.ttype == TagConstants.CASE || l.ttype == TagConstants.DEFAULT) {
                if (l.ttype == TagConstants.DEFAULT) {
                    hasDefault = true;
                }
                int loc = l.startingLoc;
                int ttype = l.ttype;
                l.getNextToken(); // Discard CASE TagConstants.or DEFAULT
                Expr e = (ttype == TagConstants.CASE ? parseExpression(l) : null);
                expect(l, TagConstants.COLON);
                seqStmt.addElement( SwitchLabel.make(e, loc) );
            } 
            else {
                if (atStart) fail(l.startingLoc,"Switch body must start with a label");
                addStmt(l);
            }
            atStart = false;
        }
        if (l.ttype == TagConstants.EOF) 
            fail(l.startingLoc, "End of input in switch body");
        int closeloc = l.startingLoc;
        l.getNextToken(); // Discard '}'

        if (!hasDefault) {
            seqStmt.addElement(SwitchLabel.make(null, closeloc));
            seqStmt.addElement(BreakStmt.make(null, closeloc));
        }
        StmtVec body = StmtVec.popFromStackVector(seqStmt);
        return SwitchStmt.make(body, openloc, closeloc, value, keywordloc);
    }

    /**
     * Internal routine for parsing zero or more catch clauses.
     *
     * <p> Effects: Parses the following grammar:
     * <pre> Catches ::= { 'catch' '(' [Modifiers] Type Idn ')' Block }* </pre>
     *
     * At the start of each iteration (including the first), if the
     * first token is not <code>catch</code>, it stops trying to
     * parse, returning the (possibly empty) sequence of catch clauses
     * parsed already and leaving the token at the first token
     * following the last catch clause parsed.  If the first token is
     * <code>catch</code>, then it tries to parse a catch clause,
     * throwing an exception if a syntax error is found.
     */
    //@ requires l != null && l.m_in != null
    private CatchClauseVec parseCatches(Lex l) {
        if (l.ttype != TagConstants.CATCH) return null;
        seqCatchClause.push();

        do {
            int loc = l.startingLoc;
            l.getNextToken(); // Discard CATCH
            expect(l, TagConstants.LPAREN);
            FormalParaDecl arg = parseFormalParaDecl(l);
            expect(l, TagConstants.RPAREN);
            seqCatchClause.addElement( CatchClause.make(arg, parseBlock(l,false),
                                                        loc) );
        } while (l.ttype == TagConstants.CATCH);
        return CatchClauseVec.popFromStackVector(seqCatchClause);
    }

    /**
     * Internal routine for parsing variable declarations
     * <em>after</em> the leading type has been parsed.
     * 
     * <p>Effects: Parses the following grammar:
     * <pre>
     * VarDeclRemainder ::=
     * { Idn { '[' ']' }* [ '=' VariableInitializer ] },*
     * </pre>
     * 
     * <p> Each <code>VarDeclRemainder</code> found is combined with
     * <code>basetype</code> to create a <code>VarDeclStmt</code>
     * which is added to the end of <code>seqStmt</code>.
     * 
     * <p> On entry, it assumes at least one
     * <code>VarDeclRemainder</code> is available, and throws an
     * exception if one isn't.  At the end of each iteration, it stops
     * trying to parse if the comma is not present, leaving the token
     * at the first token following the last
     * <code>VarDeclRemainder</code> parsed.  If a comma is found,
     * then it tries to parse the next <code>VarDeclRemainder</code>,
     * throwing an exception if a syntax error is found.
     */
    //@ requires l != null && basetype != null && l.m_in != null
    //@ requires basetype.syntax
    private void addVarDeclStmts(Lex l, int modifiers, 
                                 ModifierPragmaVec modifierPragmas,
                                 Type basetype)
    {
        // make modifierPragmas non-null, so can retroactively extend
        if( modifierPragmas == null )
            modifierPragmas = ModifierPragmaVec.make();

        for(;;) {
            // Get identifier and any [] pairs trailing it
            Identifier id = l.identifierVal;
            int locId = l.startingLoc;
            expect(l, TagConstants.IDENT);
            Type vartype = parseBracketPairs(l, basetype);

            // Get initializer if there is one
            VarInit init = null;
            int locAssignOp = Location.NULL;
            if (l.ttype == TagConstants.ASSIGN) {
                locAssignOp = l.startingLoc;
                l.getNextToken();
                init = parseVariableInitializer(l, false);
            }

            LocalVarDecl d
                = LocalVarDecl.make(modifiers, modifierPragmas, 
                                    id, vartype, locId, init, locAssignOp);
            seqStmt.addElement( VarDeclStmt.make(d) );

            // check if end of declaration

            if(l.ttype == TagConstants.MODIFIERPRAGMA ) {
                // if modifier pragma, retroactively add to modifierPragmas
                parseMoreModifierPragmas( l, modifierPragmas );
                return;
            } else if(l.ttype != TagConstants.COMMA ) {
                // all done - do not swallow following semicolon
                return;
            }

            expect( l, TagConstants.COMMA );
            /* And go around loop again */
        }
    }


    /**
     * Routine for parsing a single formal parameter declarations.
     * 
     * <p> Effects: Parses the following grammar:
     * <pre> FormalParaDecl ::= { [Modifiers] Type Idn ModifierPragma* } </pre>
     * returning an ASTNode representing the result.  Leaves
     * <code>l</code> pointing to the token just after the
     * <code>FormalParaDecl</code>.
     */
    //@ requires l != null && l.m_in != null
    //@ ensures \result != null
    public FormalParaDecl parseFormalParaDecl(Lex l) {
        int modifiers = parseModifiers(l);
        ModifierPragmaVec modifierPragmas = this.modifierPragmas;
        Type paratype = parseType(l);
        Identifier idn = l.identifierVal;
        int locId = l.startingLoc;
        expect(l, TagConstants.IDENT);
      
        // allow more modifier pragmas
        modifierPragmas = parseMoreModifierPragmas( l, modifierPragmas );

        return FormalParaDecl.make(modifiers, modifierPragmas, 
                                   idn, paratype, locId);
    }

    /**
     * @return true iff <code>e</code> is a Java
     * <code>StatementExpression</code> as defined in the grammar
     * given in the language spec.
     */
    //@ requires e != null
    public static boolean isStatementExpression(Expr e) {
        switch (e.getTag()) {
            case TagConstants.ASSIGN: 
            case TagConstants.ASGMUL: case TagConstants.ASGDIV: 
            case TagConstants.ASGREM: 
            case TagConstants.ASGADD: case TagConstants.ASGSUB:
            case TagConstants.ASGLSHIFT: case TagConstants.ASGRSHIFT: 
            case TagConstants.ASGURSHIFT: 
            case TagConstants.ASGBITAND:
            case TagConstants.ASGBITOR: case TagConstants.ASGBITXOR:
            case TagConstants.INC: case TagConstants.DEC: 
            case TagConstants.POSTFIXINC: case TagConstants.POSTFIXDEC:
            case TagConstants.METHODINVOCATION:
            case TagConstants.NEWINSTANCEEXPR:
                return true;
            default:
                return true; // TODO return false;
        }
    }
}
