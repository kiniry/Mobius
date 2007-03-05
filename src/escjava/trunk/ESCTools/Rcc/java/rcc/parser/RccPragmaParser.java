/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.parser;

import java.io.IOException;

import javafe.ast.ASTNode;
import javafe.ast.ExprVec;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.ast.IdentifierVec;
import javafe.ast.Type;
import javafe.parser.Lex;
import javafe.parser.Parse;
import javafe.parser.PragmaParser;
import javafe.parser.Token;
import javafe.util.Assert;
import javafe.util.CorrelatedReader;
import javafe.util.ErrorSet;
import javafe.util.Location;
import javafe.util.StackVector;
import rcc.RccOptions;
import rcc.ast.ArrayGuardModifierPragma;
import rcc.ast.GenericArgumentPragma;
import rcc.ast.GenericParameterPragma;
import rcc.ast.GuardedByModifierPragma;
import rcc.ast.HoldsStmtPragma;
import rcc.ast.NowarnPragma;
import rcc.ast.ReadOnlyModifierPragma;
import rcc.ast.RequiresModifierPragma;
import rcc.ast.TagConstants;
import rcc.ast.ThreadLocalStatusPragma;

// import rcc.ast.*;

/**
 * Grammar:
 */

public class RccPragmaParser extends Parse implements PragmaParser {

    private Lex scanner;

    StackVector seq = new StackVector();

    public RccPragmaParser() {
        scanner = new PragmaLex(new ErrorPragmaParser(
            "Nested annotation comments are not allowed"), true);
    }

    public boolean checkTag(int tag) {
        return tag == '#'; // SNF Wed Jun 30 15:49:52 1999 || tag == '*';
    }

    /**
     * rgrig: No idea what this should do. The documentation in the PragmaParser
     * interface says "todo: document this".
     */
    public javafe.ast.FieldDecl isPragmaDecl(/* @ non_null @ */Token l) {
        return null;
    }

    /**
     * * Eat any wizard inserted comment at the start of an * escjava
     * annotation.
     * <p> * * Precondition: in is not currently marked. * * Currently eats "#"
     * or "([^)]*)" if present from in.
     * <p>
     */
    private void eatWizardComment(CorrelatedReader in) throws IOException {

        in.mark(); // mark() marks before the character last read
        int cc = in.read();

        // Handle "#" wizard comment (appears as /*##foobar*/):
        if (cc == '#') {
            in.reset();
            return;
        }

        // Handle (...) comment:
        if (cc == '(') {
            // Skip up to and including the next close paren:
            do {
                cc = in.read();
                if (cc == -1) {
                    // At end-of-comment but still no close paren:
                    ErrorSet.error(
                        in.getLocation(),
                        "Badly formed wizard comment (missing `)')");
                    break;
                }
            } while (cc != ')');
            return;
        }

        // No wizard comment, so roll back our read, leaving in unchanged:
        in.reset();
    }

    public void restart(CorrelatedReader in, boolean eolComment) {
        try {
            in.read();
            eatWizardComment(in);
            scanner.restart(in);
        } catch (IOException e) {
            ErrorSet.fatal(in.getLocation(), e.toString());
        }
    }

    public void close() {
        scanner.close();
    }

    // # requires l!=null
    // @ ensures RES!=null
    public FormalParaDeclVec parseFormalParameterListNoParen(Lex l) {
        seq.push();
        // @ assume seq.elementType == type(FormalParaDecl)
        while (l.ttype != TagConstants.RBRACE) {
            l.getNextToken(); // swallow open paren or comma
            int modifiers = parseModifiers(l);
            Type type = parseType(l);
            int locId = l.startingLoc;
            Identifier id = parseIdentifier(l);
            type = parseBracketPairs(l, type);
            seq.addElement(FormalParaDecl.make(
                modifiers,
                modifierPragmas,
                id,
                type,
                locId));
            if (l.ttype != TagConstants.RBRACE && l.ttype != TagConstants.COMMA)
                fail(l.startingLoc, "Expected comma or }");
        }
        expect(l, TagConstants.RBRACE);
        return FormalParaDeclVec.popFromStackVector(seq);
    }

    /** this deals with ignoring pragmas in the -ignoreAnnFile switch */

    public boolean getNextPragma(Token dst) {
        while (reallyGetNextPragma(dst)) {
            String locs = "";
            if (dst.auxVal != null && dst.auxVal instanceof ASTNode) {
                int loc = ((ASTNode) dst.auxVal).getStartLoc();
                locs = Location.toFileName(loc) + " "
                    + Location.toLineNumber(loc) + " " + Location.toColumn(loc);
            }

            if (RccOptions.get().ignoreAnnSet == null
                || !RccOptions.get().ignoreAnnSet.contains(locs)) {
                // Not an annotation to ignore
                // System.out.println("Not ignoring ann at "+locs);
                return true;
            } else {
                // an annotation to ignore
                // System.out.println("Ignoring ann at "+locs);
            }
        }
        return false;
    }

    public boolean reallyGetNextPragma(Token dst) {

        if (scanner.ttype == TagConstants.EOF) {
            close();
            return false;
        }

        // Start a new pragma
        int tag;
        int loc = scanner.startingLoc;

        if (scanner.ttype == TagConstants.IDENT) {
            Identifier kw = scanner.identifierVal;
            tag = TagConstants.fromIdentifier(kw);
        } else {
            tag = scanner.ttype;
        }
        scanner.getNextToken();
        dst.startingLoc = loc;

        switch (tag) {
        case TagConstants.NOWARN:
            dst.ttype = TagConstants.LEXICALPRAGMA;
            seq.push();
            if (scanner.ttype == TagConstants.IDENT) for (;;) {
                seq.addElement(parseIdentifier(scanner));
                if (scanner.ttype != TagConstants.COMMA) break;
                scanner.getNextToken(); // Discard COMMA
            }
            IdentifierVec checks = IdentifierVec.popFromStackVector(seq);
            dst.auxVal = NowarnPragma.make(checks, loc);
            if (scanner.ttype != TagConstants.EOF)
                ErrorSet.fatal(loc, "Syntax error in nowarn pragma");
            break;

        case TagConstants.GUARDED_BY: {
            dst.ttype = TagConstants.MODIFIERPRAGMA;
            ExprVec expressions = parseExpressionList(scanner, TagConstants.EOF);
            dst.auxVal = GuardedByModifierPragma.make(expressions, loc);
            break;
        }

        case TagConstants.READONLY: {
            dst.ttype = TagConstants.MODIFIERPRAGMA;
            dst.auxVal = ReadOnlyModifierPragma.make(loc);
            break;
        }

        case TagConstants.HOLDS: {
            dst.ttype = TagConstants.STMTPRAGMA;
            ExprVec expressions = parseExpressionList(scanner, TagConstants.EOF);
            dst.auxVal = HoldsStmtPragma.make(expressions, loc);
            break;
        }

        case TagConstants.REQUIRES: {
            dst.ttype = TagConstants.MODIFIERPRAGMA;
            ExprVec expressions = parseExpressionList(scanner, TagConstants.EOF);
            dst.auxVal = RequiresModifierPragma.make(expressions, loc);
            break;
        }

        case TagConstants.ELEMS_GUARDED_BY: {
            dst.ttype = TagConstants.TYPEMODIFIERPRAGMA;
            ExprVec expressions = parseExpressionList(scanner, TagConstants.EOF);
            dst.auxVal = ArrayGuardModifierPragma.make(expressions, loc);
            break;
        }

        case TagConstants.THREAD_LOCAL: {
            dst.ttype = TagConstants.MODIFIERPRAGMA;
            dst.auxVal = ThreadLocalStatusPragma.make(true, loc);
            break;
        }

        case TagConstants.THREAD_SHARED: {
            dst.ttype = TagConstants.MODIFIERPRAGMA;
            dst.auxVal = ThreadLocalStatusPragma.make(false, loc);
            break;
        }

        case TagConstants.LBRACE:
            if (scanner.ttype == TagConstants.IDENT
                && TagConstants.fromIdentifier(scanner.identifierVal) == TagConstants.GHOST) {
                // scanner.getNextToken(); // rgrig: Check this!
                dst.ttype = TagConstants.TYPEMODIFIERPRAGMA;
                FormalParaDeclVec v = parseFormalParameterListNoParen(scanner);
                dst.auxVal = GenericParameterPragma.make(v, loc);
            } else {
                dst.ttype = TagConstants.TYPEMODIFIERPRAGMA;
                ExprVec expressions = parseExpressionList(
                    scanner,
                    TagConstants.RBRACE);
                Assert.notFalse(expressions != null);
                dst.auxVal = GenericArgumentPragma.make(expressions, loc);
            }

            break;
        default:
            ErrorSet.fatal(loc, "Unrecognized pragma" + scanner);
        }

        return true;

    }
}
