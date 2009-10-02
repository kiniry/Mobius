package javax.swing.text.html;

import java.io.*;

public class HTML$Tag {
    
    public HTML$Tag() {
        
    }
    
    protected HTML$Tag(String id) {
        this(id, false, false);
    }
    
    protected HTML$Tag(String id, boolean causesBreak, boolean isBlock) {
        
        name = id;
        this.breakTag = causesBreak;
        this.blockTag = isBlock;
    }
    
    public boolean isBlock() {
        return blockTag;
    }
    
    public boolean breaksFlow() {
        return breakTag;
    }
    
    public boolean isPreformatted() {
        return (this == PRE || this == TEXTAREA);
    }
    
    public String toString() {
        return name;
    }
    boolean blockTag;
    boolean breakTag;
    String name;
    boolean unknown;
    public static final HTML$Tag A = new HTML$Tag("a");
    public static final HTML$Tag ADDRESS = new HTML$Tag("address");
    public static final HTML$Tag APPLET = new HTML$Tag("applet");
    public static final HTML$Tag AREA = new HTML$Tag("area");
    public static final HTML$Tag B = new HTML$Tag("b");
    public static final HTML$Tag BASE = new HTML$Tag("base");
    public static final HTML$Tag BASEFONT = new HTML$Tag("basefont");
    public static final HTML$Tag BIG = new HTML$Tag("big");
    public static final HTML$Tag BLOCKQUOTE = new HTML$Tag("blockquote", true, true);
    public static final HTML$Tag BODY = new HTML$Tag("body", true, true);
    public static final HTML$Tag BR = new HTML$Tag("br", true, false);
    public static final HTML$Tag CAPTION = new HTML$Tag("caption");
    public static final HTML$Tag CENTER = new HTML$Tag("center", true, false);
    public static final HTML$Tag CITE = new HTML$Tag("cite");
    public static final HTML$Tag CODE = new HTML$Tag("code");
    public static final HTML$Tag DD = new HTML$Tag("dd", true, true);
    public static final HTML$Tag DFN = new HTML$Tag("dfn");
    public static final HTML$Tag DIR = new HTML$Tag("dir", true, true);
    public static final HTML$Tag DIV = new HTML$Tag("div", true, true);
    public static final HTML$Tag DL = new HTML$Tag("dl", true, true);
    public static final HTML$Tag DT = new HTML$Tag("dt", true, true);
    public static final HTML$Tag EM = new HTML$Tag("em");
    public static final HTML$Tag FONT = new HTML$Tag("font");
    public static final HTML$Tag FORM = new HTML$Tag("form", true, false);
    public static final HTML$Tag FRAME = new HTML$Tag("frame");
    public static final HTML$Tag FRAMESET = new HTML$Tag("frameset");
    public static final HTML$Tag H1 = new HTML$Tag("h1", true, true);
    public static final HTML$Tag H2 = new HTML$Tag("h2", true, true);
    public static final HTML$Tag H3 = new HTML$Tag("h3", true, true);
    public static final HTML$Tag H4 = new HTML$Tag("h4", true, true);
    public static final HTML$Tag H5 = new HTML$Tag("h5", true, true);
    public static final HTML$Tag H6 = new HTML$Tag("h6", true, true);
    public static final HTML$Tag HEAD = new HTML$Tag("head", true, true);
    public static final HTML$Tag HR = new HTML$Tag("hr", true, false);
    public static final HTML$Tag HTML = new HTML$Tag("html", true, false);
    public static final HTML$Tag I = new HTML$Tag("i");
    public static final HTML$Tag IMG = new HTML$Tag("img");
    public static final HTML$Tag INPUT = new HTML$Tag("input");
    public static final HTML$Tag ISINDEX = new HTML$Tag("isindex", true, false);
    public static final HTML$Tag KBD = new HTML$Tag("kbd");
    public static final HTML$Tag LI = new HTML$Tag("li", true, true);
    public static final HTML$Tag LINK = new HTML$Tag("link");
    public static final HTML$Tag MAP = new HTML$Tag("map");
    public static final HTML$Tag MENU = new HTML$Tag("menu", true, true);
    public static final HTML$Tag META = new HTML$Tag("meta");
    static final HTML$Tag NOBR = new HTML$Tag("nobr");
    public static final HTML$Tag NOFRAMES = new HTML$Tag("noframes", true, true);
    public static final HTML$Tag OBJECT = new HTML$Tag("object");
    public static final HTML$Tag OL = new HTML$Tag("ol", true, true);
    public static final HTML$Tag OPTION = new HTML$Tag("option");
    public static final HTML$Tag P = new HTML$Tag("p", true, true);
    public static final HTML$Tag PARAM = new HTML$Tag("param");
    public static final HTML$Tag PRE = new HTML$Tag("pre", true, true);
    public static final HTML$Tag SAMP = new HTML$Tag("samp");
    public static final HTML$Tag SCRIPT = new HTML$Tag("script");
    public static final HTML$Tag SELECT = new HTML$Tag("select");
    public static final HTML$Tag SMALL = new HTML$Tag("small");
    public static final HTML$Tag SPAN = new HTML$Tag("span");
    public static final HTML$Tag STRIKE = new HTML$Tag("strike");
    public static final HTML$Tag S = new HTML$Tag("s");
    public static final HTML$Tag STRONG = new HTML$Tag("strong");
    public static final HTML$Tag STYLE = new HTML$Tag("style");
    public static final HTML$Tag SUB = new HTML$Tag("sub");
    public static final HTML$Tag SUP = new HTML$Tag("sup");
    public static final HTML$Tag TABLE = new HTML$Tag("table", false, true);
    public static final HTML$Tag TD = new HTML$Tag("td", true, true);
    public static final HTML$Tag TEXTAREA = new HTML$Tag("textarea");
    public static final HTML$Tag TH = new HTML$Tag("th", true, true);
    public static final HTML$Tag TITLE = new HTML$Tag("title", true, true);
    public static final HTML$Tag TR = new HTML$Tag("tr", false, true);
    public static final HTML$Tag TT = new HTML$Tag("tt");
    public static final HTML$Tag U = new HTML$Tag("u");
    public static final HTML$Tag UL = new HTML$Tag("ul", true, true);
    public static final HTML$Tag VAR = new HTML$Tag("var");
    public static final HTML$Tag IMPLIED = new HTML$Tag("p-implied");
    public static final HTML$Tag CONTENT = new HTML$Tag("content");
    public static final HTML$Tag COMMENT = new HTML$Tag("comment");
    static final HTML$Tag[] allTags = {A, ADDRESS, APPLET, AREA, B, BASE, BASEFONT, BIG, BLOCKQUOTE, BODY, BR, CAPTION, CENTER, CITE, CODE, DD, DFN, DIR, DIV, DL, DT, EM, FONT, FORM, FRAME, FRAMESET, H1, H2, H3, H4, H5, H6, HEAD, HR, HTML, I, IMG, INPUT, ISINDEX, KBD, LI, LINK, MAP, MENU, META, NOBR, NOFRAMES, OBJECT, OL, OPTION, P, PARAM, PRE, SAMP, SCRIPT, SELECT, SMALL, SPAN, STRIKE, S, STRONG, STYLE, SUB, SUP, TABLE, TD, TEXTAREA, TH, TITLE, TR, TT, U, UL, VAR};
    static {
        HTML.getTag("html");
    }
}
