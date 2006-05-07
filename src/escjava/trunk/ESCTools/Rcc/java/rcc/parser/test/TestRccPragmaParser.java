/* Copyright 2000, 2001, Compaq Computer Corporation */


package rcc.parser.test;

import rcc.ast.RccPrettyPrint;
import rcc.ast.*;
import rcc.ast.EqualsAST;
import rcc.parser.RccPragmaParser;




import javafe.ast.PrettyPrint;
import javafe.ast.ASTNode;
import javafe.util.*;
import javafe.ast.StandardPrettyPrint;
import javafe.ast.DelegatingPrettyPrint;
import javafe.parser.Lex;
import javafe.parser.Token;
import javafe.parser.test.TestParse;

import java.io.IOException;
import javafe.ast.ExprVec;

class  RccPragmaParserWithPrint extends RccPragmaParser {
    
    public boolean getNextPragma(Token dst) {
        
        CloneWithSubstitution a=new CloneWithSubstitution(new MultipleSubstitution(SubstitutionVec.make())) ;
        
        EqualsAST e=new EqualsAST();
        
        
        
        if (!super.getNextPragma(dst)) {
            return false;
        } else {
            
            switch (((ASTNode)dst.auxVal).getTag()) {
            case TagConstants.NOWARNPRAGMA:
                break;
                
            case TagConstants.GUARDEDBYMODIFIERPRAGMA: {
                Assert.notFalse(e.equals(a.clone(((GuardedByModifierPragma)dst.auxVal).expressions,true),((GuardedByModifierPragma)dst.auxVal).expressions));
                break;
            }
            
            case TagConstants.HOLDSSTMTPRAGMA: {
                Assert.notFalse(e.
                                equals(a.clone(((HoldsStmtPragma)dst.auxVal).expressions,
                                               true),
                                       ((HoldsStmtPragma)dst.auxVal).expressions)
                                );
                break;                
            }
            
            case TagConstants.REQUIRESMODIFIERPRAGMA: {
                Assert.notFalse(e.
                                equals((ExprVec)a.
                                       clone(
                                             ((RequiresModifierPragma)dst.auxVal).expressions,
                                             true),
                                       ((RequiresModifierPragma)dst.auxVal).expressions
                                       )
                                );
                break;
            }
            
            default:
                ErrorSet.fatal(dst.startingLoc, "Unrecognized pragma" + ((ASTNode)dst.auxVal).getTag());
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
        p.del = new StandardPrettyPrint(p);
        PrettyPrint.inst = p;
        
        TestParse.lexer = new Lex(new RccPragmaParserWithPrint(), true);
        TestParse.main(argv);
    }
}
