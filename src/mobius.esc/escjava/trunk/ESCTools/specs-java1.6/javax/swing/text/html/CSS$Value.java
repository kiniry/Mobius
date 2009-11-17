package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

final class CSS$Value {
    
    private CSS$Value(String name) {
        
        this.name = name;
    }
    
    public String toString() {
        return name;
    }
    static final CSS$Value INHERITED = new CSS$Value("inherited");
    static final CSS$Value NONE = new CSS$Value("none");
    static final CSS$Value DOTTED = new CSS$Value("dotted");
    static final CSS$Value DASHED = new CSS$Value("dashed");
    static final CSS$Value SOLID = new CSS$Value("solid");
    static final CSS$Value DOUBLE = new CSS$Value("double");
    static final CSS$Value GROOVE = new CSS$Value("groove");
    static final CSS$Value RIDGE = new CSS$Value("ridge");
    static final CSS$Value INSET = new CSS$Value("inset");
    static final CSS$Value OUTSET = new CSS$Value("outset");
    static final CSS$Value BLANK_LIST_ITEM = new CSS$Value("none");
    static final CSS$Value DISC = new CSS$Value("disc");
    static final CSS$Value CIRCLE = new CSS$Value("circle");
    static final CSS$Value SQUARE = new CSS$Value("square");
    static final CSS$Value DECIMAL = new CSS$Value("decimal");
    static final CSS$Value LOWER_ROMAN = new CSS$Value("lower-roman");
    static final CSS$Value UPPER_ROMAN = new CSS$Value("upper-roman");
    static final CSS$Value LOWER_ALPHA = new CSS$Value("lower-alpha");
    static final CSS$Value UPPER_ALPHA = new CSS$Value("upper-alpha");
    static final CSS$Value BACKGROUND_NO_REPEAT = new CSS$Value("no-repeat");
    static final CSS$Value BACKGROUND_REPEAT = new CSS$Value("repeat");
    static final CSS$Value BACKGROUND_REPEAT_X = new CSS$Value("repeat-x");
    static final CSS$Value BACKGROUND_REPEAT_Y = new CSS$Value("repeat-y");
    static final CSS$Value BACKGROUND_SCROLL = new CSS$Value("scroll");
    static final CSS$Value BACKGROUND_FIXED = new CSS$Value("fixed");
    private String name;
    static final CSS$Value[] allValues = {INHERITED, NONE, DOTTED, DASHED, SOLID, DOUBLE, GROOVE, RIDGE, INSET, OUTSET, DISC, CIRCLE, SQUARE, DECIMAL, LOWER_ROMAN, UPPER_ROMAN, LOWER_ALPHA, UPPER_ALPHA, BLANK_LIST_ITEM, BACKGROUND_NO_REPEAT, BACKGROUND_REPEAT, BACKGROUND_REPEAT_X, BACKGROUND_REPEAT_Y, BACKGROUND_FIXED, BACKGROUND_FIXED};
}
