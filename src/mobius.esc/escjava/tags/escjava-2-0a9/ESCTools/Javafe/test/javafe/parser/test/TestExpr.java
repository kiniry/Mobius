/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser.test;

import java.io.IOException;
import javafe.ast.*;
import javafe.parser.*;
import javafe.parser.TagConstants;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.FileCorrelatedReader;
import javafe.util.Location;

// Test harness for expressions.

public class TestExpr
{
    //@ ensures false;
    public static void fatal(String msg) {
	System.err.println("Fatal error: " + msg);
	System.exit(99);
    }

    //@ requires \nonnullelements(argv);
    public static void main(String[] argv) {
        boolean compare = false;
        boolean check = false;

        for(int i = 0; i < argv.length; i++) {
            if (argv[i].equals("compare")) compare = true;
            else if (argv[i].equals("check")) check = true;
            else fatal("Bad argument.");
        }

        Lex l = new Lex(null, true);
        l.restart(new FileCorrelatedReader(System.in, "stdin"));
        Parse p = new Parse();

        for(;;) {
            Expr e1 = p.parseExpression(l);
            if (check) e1.check();
            if (compare) {
                p.expect(l, TagConstants.COMMA);
                Expr e2 = p.parseExpression(l);
                if (check) e2.check();
                if (! compare(e1, e2))
                    ErrorSet.fatal(e2.getStartLoc(),
                                   "Expressions differ: " + e1.toString()
                                   + " versus " + e2.toString());
            }
            if (l.ttype == TagConstants.EOF) System.exit(0);
            p.expect(l, TagConstants.COMMA);
        }
    }

    //@ requires n1 != null && n2 != null;
    private static boolean compare( ASTNode n1, ASTNode n2 ) {

        // Ignores parens

        if( n1 instanceof ParenExpr ) {
            return compare( ((ParenExpr)n1).expr, n2 );
        } 
        else if( n2 instanceof ParenExpr ) {
            return compare( n1, ((ParenExpr)n2).expr );
        }
        else if( n1.getTag() != n2.getTag() ) {
            System.out.println("Tags differ: "+n1.getTag()+" "+n2.getTag() );
            return false;
        }
        else {

            try {
                for(int i=0;;i++) {
                    Object e1 = n1.childAt(i);
                    Object e2 = n2.childAt(i);
        
                    if( (e1 instanceof ASTNode) && (e2 instanceof ASTNode) ) {
                        // Compare them
                        if( !compare( (ASTNode)e1, (ASTNode)e2 ) ) {
                            System.out.println("Tag "+n1.getTag()
                                               +" elems at index "+i+" differ");
                            return false;
                        }
                    }
                }
            } catch( IndexOutOfBoundsException e ) {
                // Nothing different, so
                return true;
            }
        }
    }
}
