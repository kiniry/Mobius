package escjava.vcGeneration;

import java.lang.StringBuffer;

public class StringBufferWrapper {

    private final String TAB = "  ";
    private final String LBR = "(";
    private final String RBR = ")";
    private final String NL = "\n";
    
    /*@ non_null @*/StringBuffer out = null;

    /*@ non_null @*/StringBuffer indentation = null;

    public StringBufferWrapper(StringBuffer out) {
        this.out = out;
        indentation = new StringBuffer();
    }

    /*
     * just append the parameter, N stands for normal
     */
    public /*@ non_null @*/StringBuffer appendN(/*@ non_null @*/String s) {
        out.append(s);

        return out;
    }

    /*
     * append indentation and parameter
     */
    public /*@ non_null @*/StringBuffer append(/*@ non_null @*/String s) {
        out.append(indentation);
        out.append(s);

        return out;
    }

    /*
     * This function goes to next line, increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */
    public /*@ non_null @*/StringBuffer appendI(/*@ non_null @*/String s) {

        if (indentation.length() != 0) { // not first call
            out.append(NL);
            out.append(indentation);
        }

        indentation.append(TAB);

        out.append(LBR + s);

        return out;
    }

    /*
     * This function increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */
    public /*@ non_null @*/StringBuffer appendIwNl(/*@ non_null @*/String s) {
        indentation.append(TAB);
        out.append(indentation);
        out.append(LBR + s);

        return out;
    }

    /*
     * This function goes to new line, add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */
    public /*@ non_null @*/StringBuffer reduceI() {
        out.append(NL);
        indentation = indentation.delete(0, TAB.length());
        out.append(indentation + RBR);

        return out;
    }

    /*
     * This function add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */
    public /*@ non_null @*/StringBuffer reduceIwNl() {
        out.append(RBR);
        indentation = indentation.delete(0, TAB.length());

        return out;
    }

    public/*@ non_null @*/String toString() {
        return out.toString();
    }

}
