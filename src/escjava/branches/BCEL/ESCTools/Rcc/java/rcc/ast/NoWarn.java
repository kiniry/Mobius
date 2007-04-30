/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import java.util.Hashtable;

import javafe.ast.CompilationUnit;
import javafe.ast.LexicalPragma;
import javafe.ast.LexicalPragmaVec;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Location;

/**
 * * Handles turning off warnings.
 */

public class NoWarn {

    // TODO: Comment this!
    // TODO: Check this!
    public static void init() { /* do nothing */ }

    /***************************************************************************
     * * Global nowarns: * *
     **************************************************************************/

    static private int chkStatus[] = new int[TagConstants.LASTRCCCHECKTAG
        - TagConstants.FIRSTRCCCHECKTAG];

    static private Hashtable packageNoWarns = new Hashtable();

    static {
        for (int i = TagConstants.FIRSTRCCCHECKTAG; i < TagConstants.LASTRCCCHECKTAG; i++) {
            setChkStatus(i, TagConstants.CHK_AS_ASSERT);
        }
    }

    public static void reset() {
        for (int i = TagConstants.FIRSTRCCCHECKTAG; i < TagConstants.LASTRCCCHECKTAG; i++) {
            setChkStatus(i, TagConstants.CHK_AS_ASSERT);
        }
    }

    /**
     * Sets how the check tag should be interpreted. tag should be one of the
     * CHK... constants defined in TagConstants, and status should be one of
     * CHK_AS_ASSUME/CHK_AS_ASSERT/CHK_AS_SKIP
     */

    public static void setChkStatus(int tag, int status) {

        Assert.notFalse(TagConstants.FIRSTRCCCHECKTAG <= tag
            && tag < TagConstants.LASTRCCCHECKTAG);

        Assert.notFalse(status == TagConstants.CHK_AS_ASSUME
            || status == TagConstants.CHK_AS_ASSERT
            || status == TagConstants.CHK_AS_SKIP);

        chkStatus[tag - TagConstants.FIRSTRCCCHECKTAG] = status;
    }

    /**
     * Returns how the check tag should be interpreted. tag should be one of the
     * CHK... constants defined in TagConstants. The result is be one of
     * CHK_AS_ASSUME/CHK_AS_ASSERT/CHK_AS_SKIP.
     */

    public static int getChkStatus(int tag) {

        Assert.notFalse(TagConstants.FIRSTRCCCHECKTAG <= tag
            && tag <= TagConstants.LASTRCCCHECKTAG);

        return chkStatus[tag - TagConstants.FIRSTRCCCHECKTAG];
    }

    public static void setPackageStatus(String name, int status) {

        Assert.notFalse(status == TagConstants.CHK_AS_ASSUME
            || status == TagConstants.CHK_AS_ASSERT
            || status == TagConstants.CHK_AS_SKIP);

        packageNoWarns.put(name, new Integer(status));
    }

    public static int getPackageStatus(String name) {
        while (true) {
            Integer status = (Integer) packageNoWarns.get(name);
            int lastDot;
            if (status != null) { return status.intValue(); }
            lastDot = name.lastIndexOf('.');
            if (lastDot == -1) break;
            name = name.substring(0, lastDot);
        }
        return TagConstants.CHK_AS_ASSERT;
    }

    /**
     * * Convert a nowarn category to its tag. Returns 0 if the String * is not
     * a valid nowarn category.
     */
    public static int toNoWarnTag(String name) {
        for (int i = TagConstants.FIRSTRCCCHECKTAG; i < TagConstants.LASTRCCCHECKTAG; i++) {
            if (TagConstants.toString(i).equals(name)) return i;
        }

        return 0;
    }

    /*
     * The line # and streamId to nowarn before (cf. setStartLine).
     */
    private static int noWarnStreamId = -1;

    private static int startLine = -1; // no nowarn by default

    /**
     * * Set a nowarn to ignore all lines before a given line in a given *
     * CompilationUnit.
     * <p> * * Future calls to this routine remove any previous nowarns *
     * established via this routine.
     * <p> * * Passing a line # of -1 acts as a no-op nowarn.
     * <p>
     */
    // @ requires cu!=null
    public static void setStartLine(int line, CompilationUnit cu) {
        startLine = line;
        noWarnStreamId = Location.toStreamId(cu.loc);
    }

    /***************************************************************************
     * * Registering nowarns annotations: * *
     **************************************************************************/

    static private LexicalPragmaVec nowarns = LexicalPragmaVec.make();

    public static void registerNowarns(LexicalPragmaVec v) {
        if (v != null) nowarns.append(v);
    }

    /***************************************************************************
     * * Comparing locations: * *
     **************************************************************************/

    /**
     * * Is <code>loc</code> on a given line number in a given stream?
     * <p> * * <code>loc</code> may be <code>Location.NULL</code>, in which *
     * case <code>false</code> is returned.
     */
    static boolean onLine(int loc, int lineNo, int streamId) {
        if (loc == Location.NULL) return false;

        return (streamId == Location.toStreamId(loc))
            && (lineNo == Location.toLineNumber(loc));
    }

    /**
     * * Is a given line # in a given stream (id) before (exclusive) * the line
     * that contains a given location?
     * <p> * * If loc is Location.NULL, then no is returned.
     * <p>
     */
    static boolean beforeLine(int loc, int lineNo, int streamId) {
        if (loc == Location.NULL) return false;

        if (Location.toStreamId(loc) != streamId) return false;

        return (Location.toLineNumber(loc) < lineNo);
    }

    /**
     * * Is a given line # in a given stream (id) between the lines that *
     * contain the two given locations (inclusive)?
     * <p> * * If either loc is Location.NULL, then no is returned.
     * <p> * * Precondition: the two locations must be from the same stream.
     */
    static boolean inRange(int startLoc, int endLoc, int lineNo, int streamId) {
        if (startLoc == Location.NULL || endLoc == Location.NULL) return false;

        // Check startLoc...endLoc in streamId:
        if (Location.toStreamId(startLoc) != streamId) return false;
        Assert.notFalse(Location.toStreamId(endLoc) == streamId);

        return (Location.toLineNumber(startLoc) <= lineNo)
            && (lineNo <= Location.toLineNumber(endLoc));
    }

    /***************************************************************************
     * * Check nonwarn status: * *
     **************************************************************************/

    /**
     * Returns how the check tag should be interpreted. tag should be one of the
     * CHK... constants defined in TagConstants. The result is one of
     * CHK_AS_ASSUME/CHK_AS_ASSERT/CHK_AS_SKIP.
     */

    public static int getChkStatus(int tag, int locUse, int locPragmaDecl) {
        Assert.notFalse(TagConstants.FIRSTRCCCHECKTAG <= tag
            && tag <= TagConstants.LASTRCCCHECKTAG);

        // If uncommented, display the ranges of each check:
        // displayWarningRange(tag, locUse, locPragmaDecl);

        // Check for startLine nowarn:
        if (beforeLine(locUse, startLine, noWarnStreamId))
            return TagConstants.CHK_AS_ASSUME;

        // check nowarns
        for (int i = 0; i < nowarns.size(); i++) {
            LexicalPragma lp = nowarns.elementAt(i);
            if (lp instanceof NowarnPragma) {

                NowarnPragma np = (NowarnPragma) lp;
                int nowarnStreamId = Location.toStreamId(np.loc);
                int nowarnLineNo = Location.toLineNumber(np.loc);

                if (onLine(locUse, nowarnLineNo, nowarnStreamId)
                    || onLine(locPragmaDecl, nowarnLineNo, nowarnStreamId)) {
                    // on same line
                    if (np.checks == null || np.checks.size() == 0) {
                        // applies to all checks
                        np.triggered = true;
                        return TagConstants.CHK_AS_ASSUME;
                    }

                    // search thru listed checks
                    String chkStr = TagConstants.toString(tag);

                    for (int j = 0; j < np.checks.size(); j++)
                        if (chkStr.equals(np.checks.elementAt(j).toString())) {
                            // no warn on this tag
                            np.triggered = true;
                            return TagConstants.CHK_AS_ASSUME;
                        }
                }
            }
        }

        // no line-specific nowarn
        // check general table

        return chkStatus[tag - TagConstants.FIRSTRCCCHECKTAG];
    }

    /**
     * Routine to display ranges of checks for debugging use:
     */
    /*
    private static void displayWarningRange(
        int tag,
        int locUse,
        int locPragmaDecl) {
        if (!Info.on) return;

        Info.out("[Will check a possible error of type "
            + TagConstants.toString(tag) + ":");

        ErrorSet.caution(locUse, "Use location:");

        if (locPragmaDecl != Location.NULL) {
            ErrorSet.caution(locPragmaDecl, "Declaration location:");
        }

        Info.out("]");
    }
    */

    static public void displayUntriggeredNowarns() {
        for (int i = 0; i < nowarns.size(); i++) {
            LexicalPragma lp = nowarns.elementAt(i);
            if (lp instanceof NowarnPragma) {
                NowarnPragma np = (NowarnPragma) lp;
                if (!np.triggered) {
                    ErrorSet.warning(np.loc, "untriggered no_warn");
                }
            }
        }
    }
}
