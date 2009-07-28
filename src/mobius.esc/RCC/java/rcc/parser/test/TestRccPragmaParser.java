/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.parser.test;

import java.io.IOException;

import javafe.ast.ASTNode;
import javafe.ast.DelegatingPrettyPrint;
import javafe.ast.PrettyPrint;
import javafe.ast.StandardPrettyPrint;
import javafe.parser.Lex;
import javafe.parser.Token;
import javafe.parser.test.TestParse;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import rcc.ast.CloneWithSubstitution;
import rcc.ast.EqualsAST;
import rcc.ast.GuardedByModifierPragma;
import rcc.ast.HoldsStmtPragma;
import rcc.ast.MultipleSubstitution;
import rcc.ast.RccPrettyPrint;
import rcc.ast.RequiresModifierPragma;
import rcc.ast.SubstitutionVec;
import rcc.ast.TagConstants;
import rcc.parser.RccPragmaParser;

class RccPragmaParserWithPrint extends RccPragmaParser {

    public boolean getNextPragma(Token dst) {

        CloneWithSubstitution a = new CloneWithSubstitution(
            new MultipleSubstitution(SubstitutionVec.make()));

        EqualsAST e = new EqualsAST();

        if (!super.getNextPragma(dst)) {
            return false;
        } else {

            switch (((ASTNode) dst.auxVal).getTag()) {
            case TagConstants.NOWARNPRAGMA:
                break;

            case TagConstants.GUARDEDBYMODIFIERPRAGMA: {
                Assert.notFalse(e.equals(a.clone(
                    ((GuardedByModifierPragma) dst.auxVal).expressions,
                    true), ((GuardedByModifierPragma) dst.auxVal).expressions));
                break;
            }

            case TagConstants.HOLDSSTMTPRAGMA: {
                Assert.notFalse(e.equals(a.clone(
                    ((HoldsStmtPragma) dst.auxVal).expressions,
                    true), ((HoldsStmtPragma) dst.auxVal).expressions));
                break;
            }

            case TagConstants.REQUIRESMODIFIERPRAGMA: {
                Assert.notFalse(e.equals(a.clone(
                    ((RequiresModifierPragma) dst.auxVal).expressions,
                    true), ((RequiresModifierPragma) dst.auxVal).expressions));
                break;
            }

            default:
                ErrorSet.fatal(dst.startingLoc, "Unrecognized pragma"
                    + ((ASTNode) dst.auxVal).getTag());
            }

            return true;
        }

    }
}

public class TestRccPragmaParser {
    public static void main(String[] argv) throws IOException {

        // DelegatingPrettyPrint p = new javafe.tc.TypePrint();
        // p.del = new RccPrettyPrint(p, new StandardPrettyPrint(p));
        DelegatingPrettyPrint p = new RccPrettyPrint();
        p.setDel(new StandardPrettyPrint(p));
        PrettyPrint.inst = p;

        TestParse.lexer = new Lex(new RccPragmaParserWithPrint(), true);
        TestParse.main(argv);
    }
}
