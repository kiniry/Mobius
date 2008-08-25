/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.parser;

import javafe.ast.*;
import rcc.ast.*;
import rcc.ast.TagConstants;

import javafe.parser.Lex;
import javafe.parser.PragmaParser;
import javafe.parser.Token;
import javafe.parser.Parse;
import javafe.util.Location;
import javafe.util.CorrelatedReader;
import javafe.util.ErrorSet;
import javafe.util.Assert;

import java.io.IOException;


class PragmaLex  extends Lex {
    
    public static final int  hash = 10000;   //  how do I pick this number?
    
    PragmaLex(PragmaParser p, boolean b) {
        super(p, b);
        addPunctuation("#",hash);
    }
    
    public int  getNextToken() {
        if (super.getNextToken()==hash) {
            int loc = startingLoc;
            Parse p = new Parse();
            p.expect(this, TagConstants.ELEMS_GUARDED_BY);
            ExprVec expressions = ExprVec.make();
            while (true) {
                expressions.addElement( p.parseExpression(this) );
                if( ttype != TagConstants.COMMA ) {
                    break;
                }
                getNextToken();
            }
            ttype = javafe.parser.TagConstants.TYPEMODIFIERPRAGMA;
            auxVal =
                ArrayGuardModifierPragma.make(
                                              expressions,
                                              loc);
        }
        return ttype;
    }
    
}

