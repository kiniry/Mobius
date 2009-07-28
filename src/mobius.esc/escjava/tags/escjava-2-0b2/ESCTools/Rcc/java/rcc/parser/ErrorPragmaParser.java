/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.parser;

import java.io.IOException;

import javafe.parser.PragmaParser;
import javafe.parser.Token;
import javafe.util.CorrelatedReader;
import javafe.util.ErrorSet;

/**
 * * This class produces a PragmaParser that reports an client-choosen * error
 * message each time an annotation comment is encountered. * (Javadoc comments
 * are also considered annotations.)
 */

public class ErrorPragmaParser implements PragmaParser {

    /**
     * rgrig: No idea what this should do. The documentation in the PragmaParser
     * interface says "todo: document this".
     */
    public javafe.ast.FieldDecl isPragmaDecl(/* @ non_null @ */Token l) {
        return null;
    }

    /** The error message to report * */
    public String msg;

    /** Create a new ErrorPragmaParser that report error message msg * */
    public ErrorPragmaParser(String msg) {
        this.msg = msg;
    }

    public boolean checkTag(int tag) {
        return tag == '@'; // SNF || tag == '*';
    }

    /** Report an error for each annotation comment * */
    public void restart(CorrelatedReader in, boolean eolComment) {
        try {
            in.read();
        } catch (IOException e) {
            ErrorSet.fatal(in.getLocation(), e.toString());
        }

        ErrorSet.error(in.getLocation(), msg);
    }

    /** Produce no actual pragmas * */
    public boolean getNextPragma(Token dst) {
        return false;
    }

    /** No work to close us * */
    public void close() { /* do nothing */ }
}
