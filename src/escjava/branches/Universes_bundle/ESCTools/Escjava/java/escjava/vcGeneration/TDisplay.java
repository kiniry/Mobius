package escjava.vcGeneration;

public class TDisplay {

    private static boolean err;

    private static boolean warn;

    private static boolean info;

    private static boolean colors;

    static/*@ non_null @*/String errPrompt;

    static/*@ non_null @*/String warnPrompt;

    static/*@ non_null @*/String infoPrompt;

    static public void init(boolean err, boolean warn, boolean info, boolean colors) {

        TDisplay.err = err;
        TDisplay.warn = warn;
        TDisplay.info = info;
        TDisplay.colors = colors;

        if (!colors) {
            TDisplay.errPrompt = "Err ";
            TDisplay.warnPrompt = "Warning ";
        } else {
            TDisplay.errPrompt = "\033[31m>\033[0;m ";
            TDisplay.warnPrompt = "\033[33m>\033[0;m ";
        }

    }

    public static void err(/*@ non_null @*/Object o, /*@ non_null @*/String method, String err) {

        if (TDisplay.err) {
            System.err.println(errPrompt + o.getClass().getName() + "."
                    + method);
            System.err.println("  " + err);
        }
    }

    public static void warn(/*@ non_null @*/Object o, /*@ non_null @*/String method, String warn) {

        if (TDisplay.warn) {
            System.err.println(warnPrompt + o.getClass().getName() + "."
                    + method);
            System.err.println("  " + warn);
        }
    }

    public static void info(/*@ non_null @*/Object o, /*@ non_null @*/String method, String info) {

        if (TDisplay.info) {
            System.err.println("[" + o.getClass().getName() + "." + method
                    + "]");
            System.err.println("[" + info + "]");
        }

    }

    public static void err(/*@ non_null @*/String o, /*@ non_null @*/String method, String err) {

        if (TDisplay.err) {
            System.err.println(errPrompt + o + "." + method);
            System.err.println("  " + err);
        }

    }

    public static void warn(/*@ non_null @*/String o, /*@ non_null @*/String method, String warn) {

        if (TDisplay.warn) {
            System.err.println(warnPrompt + o + "." + method);
            System.err.println("  " + warn);
        }

    }

    public static void info(/*@ non_null @*/String o, /*@ non_null @*/String method, String info) {

        if (TDisplay.info) {
            System.err.println("[" + o + "." + method + "]");
            System.err.println("[" + info + "]");
        }

    }

}
