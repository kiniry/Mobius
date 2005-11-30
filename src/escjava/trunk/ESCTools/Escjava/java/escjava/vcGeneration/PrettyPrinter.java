package escjava.vcGeneration;

import java.io.*;

public class PrettyPrinter {

    private final String TAB;
    private final String LBR;
    private final String RBR;
    private final String NL;
    
    /*@ non_null @*/Writer out = null;

    /*@ non_null @*/StringBuffer indentation = null;

    public PrettyPrinter(Writer out, String tab, String lbr, String rbr, String nl) {
        this.out = out;
        indentation = new StringBuffer();
        TAB = tab;
        LBR = lbr;
        RBR = rbr;
        NL = nl;
    }

    /**
     * just append the parameter, N stands for normal
     */
    public/*@ non_null @*/Writer appendN(/*@ non_null @*/String s) throws IOException {
        out.write(s);

        return out;
    }

    /**
     * append indentation and parameter
     */
    public/*@ non_null @*/Writer append(/*@ non_null @*/String s) throws IOException {
        out.write(indentation.toString());
        out.write(s);

        return out;
    }

    /**
     * This function goes to next line, increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */
    public/*@ non_null @*/Writer appendI(/*@ non_null @*/String s) throws IOException {
        if (indentation.length() != 0) { // not first call
            out.write(NL);
            out.write(indentation.toString());
        }

        indentation.append(TAB);

        out.write(LBR + s);
        return out;
    }

    /**
     * This function increases indentation by two spaces
     * and add a '('
     * If you want to change the indentation style do it here.
     */
    public/*@ non_null @*/Writer appendIwNl(/*@ non_null @*/String s) throws IOException {
        indentation.append(TAB);
        out.write(indentation.toString());
        out.write(LBR + s);

        return out;
    }

    /**
     * This function goes to new line, add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */
    public/*@ non_null @*/Writer reduceI() throws IOException {
        out.write(NL);
        indentation = indentation.delete(0, TAB.length());
        out.write(indentation + RBR);

        return out;
    }

    /**
     * This function add a ')' and
     * reduces indentation by two spaces
     * If you want to change the indentation style do it here.
     */
    public/*@ non_null @*/Writer reduceIwNl() throws IOException {
        out.write(RBR);
        indentation = indentation.delete(0, TAB.length());

        return out;
    }

    public/*@ non_null @*/String toString() {
        return out.toString();
    }

}
