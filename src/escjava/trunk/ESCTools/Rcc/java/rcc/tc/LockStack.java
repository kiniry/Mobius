/* Copyright 2000, 2001, Compaq Computer Corporation */


// SNF Tue Jul  6 11:32:42 1999

package rcc.tc;

import java.lang.Integer;
import rcc.ast.IntegerVec;
import rcc.ast.*;
import rcc.ast.TagConstants;
import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;

class LockStack {
    private EqualsAST equality = new EqualsAST();
    
    private IntegerVec  marks;
    private javafe.ast.ExprVec locks;
    LockStack() {
        marks = IntegerVec.make();
        locks = ExprVec.make();
    }
    
    public void push(Expr e) {
        locks.addElement(e);
    }
    
    public void popToMark() {
        Assert.notFalse(marks.size() > 0);
        int x = marks.pop().intValue();
        while (locks.size() != x) {
            locks.pop();
        }
    }
    
    public boolean  contains(Expr e) {
        for (int i = 0; i<locks.size(); i++) {
            if (equality.equals(e,locks.elementAt(i))) {
                return true;
            }
        }
        return false;

    }
    
    public void mark() {
        marks.addElement(new Integer(locks.size()));
    }
    
    public String toString() {
               return PrettyPrint.inst.toString(locks);
    }

    public String expressionsToString() {
        String s = ""; 
        for (int i = 0; i < locks.size(); i++) {
            s = s + locks.elementAt(i); 
        }
        return s;
    }
    
}






