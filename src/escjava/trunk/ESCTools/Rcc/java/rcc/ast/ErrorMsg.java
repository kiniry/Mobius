/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.tc.TypeSig;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Location;
import rcc.RccOptions;

/**
 * * Provides printing of error messages to the user.
 */

public final class ErrorMsg {

    public static void print(
        TypeSig sig,
        String s,
        int loc,
        String extra,
        int declLoc) {
        if (sig == null
            || NoWarn.getPackageStatus(sig.getPackageName()) == TagConstants.CHK_AS_ASSERT) {
            print(s, loc, extra, declLoc);
        }
    }

    public static void print(
        TypeSig sig1,
        TypeSig sig2,
        String s,
        int loc,
        String extra,
        int declLoc) {
        if ((sig1 == null || NoWarn.getPackageStatus(sig1.getPackageName()) == TagConstants.CHK_AS_ASSERT)
            && (sig2 == null || NoWarn.getPackageStatus(sig2.getPackageName()) == TagConstants.CHK_AS_ASSERT)) {
            print(s, loc, extra, declLoc);
        }
    }

    public static void print(String s, int loc, String extra, int declLoc) {

        int tag = TagConstants.checkFromString(s);
        String msg = chkToMsg(tag, loc);

        Assert.notFalse(loc != Location.NULL);
        switch (NoWarn.getChkStatus(tag, loc, declLoc)) {
        case TagConstants.CHK_AS_ASSUME:
            return;
        case TagConstants.CHK_AS_ASSERT:
            break;
        case TagConstants.CHK_AS_SKIP:
            return;
        default:
            Assert.fail("unreachable");
        }

        if (RccOptions.get().tse) {
            try {
                throw new Exception();
            } catch (Exception e) {
                System.out.println("Stack trace:");
                e.printStackTrace();
            }
        }

        ErrorSet.warning(loc, msg + " " + extra + " ("
            + TagConstants.toString(tag) + ")");

        if (declLoc != Location.NULL && !Location.isWholeFileLoc(declLoc)) {
            System.out.println("Associated declaration is "
                + Location.toString(declLoc) + ":");
            ErrorSet.displayColumn(declLoc);
        }

        if (RccOptions.get().suggest) {
            System.out.println("Suggestion [" + Location.toLineNumber(loc)
                + "," + Location.toColumn(loc) + "]: " + "none\n");
        }

    }

    private static String chkToMsg(int tag, int declLoc) {
        String r = null;
        // Finally, describe the error
        switch (tag) {
        case TagConstants.CHKCONSTANTLOCKS:
            r = ("lock expression may not be constant. ");
            Assert.notFalse(declLoc != Location.NULL);
            break;
        case TagConstants.CHKMODIFIERS:
            r = ("incorrect use of annotation. ");
            Assert.notFalse(declLoc != Location.NULL);
            break;

        case TagConstants.CHKSUPER:
            r = ("requires set must be a subset of superclass method's. ");
            // SNF Thu Jul 22 09:51:43 1999 Assert.notFalse(declLoc !=
            // Location.NULL);
            break;

        case TagConstants.CHKRACE:
            r = ("possible race condition. ");
            // SNF Thu Jul 22 09:51:43 1999 Assert.notFalse(declLoc !=
            // Location.NULL);
            break;

        case TagConstants.CHKLOCAL:
            r = (""); // concat this onto something
            // SNF Thu Jul 22 09:51:43 1999 Assert.notFalse(declLoc !=
            // Location.NULL);
            break;

        case TagConstants.CHKOVERRIDE:
            r = ("a local class cannot override method from shared class: ");
            // SNF Thu Jul 22 09:51:43 1999 Assert.notFalse(declLoc !=
            // Location.NULL);
            break;

        case TagConstants.CHKBADCAST:
            r = ("suspicious type error. ");
            break;

        case TagConstants.CHKMSG:
            r = ("");
            break;

        case TagConstants.CHKREADONLY:
            r = ("");
            break;

        case TagConstants.CHKSHAREDARRAY:
        case TagConstants.CHKSHAREDFIELD:
        case TagConstants.CHKSTATICFIELD:
            r = ("");
            break;

        default:
            // @ unreachable
            Assert.fail("Bad tag");
            break;
        }
        return r;
    }

}
