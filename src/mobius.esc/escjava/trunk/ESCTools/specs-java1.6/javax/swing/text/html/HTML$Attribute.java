package javax.swing.text.html;

import java.io.*;

public final class HTML$Attribute {
    
    HTML$Attribute(String id) {
        
        name = id;
    }
    
    public String toString() {
        return name;
    }
    private String name;
    public static final HTML$Attribute SIZE = new HTML$Attribute("size");
    public static final HTML$Attribute COLOR = new HTML$Attribute("color");
    public static final HTML$Attribute CLEAR = new HTML$Attribute("clear");
    public static final HTML$Attribute BACKGROUND = new HTML$Attribute("background");
    public static final HTML$Attribute BGCOLOR = new HTML$Attribute("bgcolor");
    public static final HTML$Attribute TEXT = new HTML$Attribute("text");
    public static final HTML$Attribute LINK = new HTML$Attribute("link");
    public static final HTML$Attribute VLINK = new HTML$Attribute("vlink");
    public static final HTML$Attribute ALINK = new HTML$Attribute("alink");
    public static final HTML$Attribute WIDTH = new HTML$Attribute("width");
    public static final HTML$Attribute HEIGHT = new HTML$Attribute("height");
    public static final HTML$Attribute ALIGN = new HTML$Attribute("align");
    public static final HTML$Attribute NAME = new HTML$Attribute("name");
    public static final HTML$Attribute HREF = new HTML$Attribute("href");
    public static final HTML$Attribute REL = new HTML$Attribute("rel");
    public static final HTML$Attribute REV = new HTML$Attribute("rev");
    public static final HTML$Attribute TITLE = new HTML$Attribute("title");
    public static final HTML$Attribute TARGET = new HTML$Attribute("target");
    public static final HTML$Attribute SHAPE = new HTML$Attribute("shape");
    public static final HTML$Attribute COORDS = new HTML$Attribute("coords");
    public static final HTML$Attribute ISMAP = new HTML$Attribute("ismap");
    public static final HTML$Attribute NOHREF = new HTML$Attribute("nohref");
    public static final HTML$Attribute ALT = new HTML$Attribute("alt");
    public static final HTML$Attribute ID = new HTML$Attribute("id");
    public static final HTML$Attribute SRC = new HTML$Attribute("src");
    public static final HTML$Attribute HSPACE = new HTML$Attribute("hspace");
    public static final HTML$Attribute VSPACE = new HTML$Attribute("vspace");
    public static final HTML$Attribute USEMAP = new HTML$Attribute("usemap");
    public static final HTML$Attribute LOWSRC = new HTML$Attribute("lowsrc");
    public static final HTML$Attribute CODEBASE = new HTML$Attribute("codebase");
    public static final HTML$Attribute CODE = new HTML$Attribute("code");
    public static final HTML$Attribute ARCHIVE = new HTML$Attribute("archive");
    public static final HTML$Attribute VALUE = new HTML$Attribute("value");
    public static final HTML$Attribute VALUETYPE = new HTML$Attribute("valuetype");
    public static final HTML$Attribute TYPE = new HTML$Attribute("type");
    public static final HTML$Attribute CLASS = new HTML$Attribute("class");
    public static final HTML$Attribute STYLE = new HTML$Attribute("style");
    public static final HTML$Attribute LANG = new HTML$Attribute("lang");
    public static final HTML$Attribute FACE = new HTML$Attribute("face");
    public static final HTML$Attribute DIR = new HTML$Attribute("dir");
    public static final HTML$Attribute DECLARE = new HTML$Attribute("declare");
    public static final HTML$Attribute CLASSID = new HTML$Attribute("classid");
    public static final HTML$Attribute DATA = new HTML$Attribute("data");
    public static final HTML$Attribute CODETYPE = new HTML$Attribute("codetype");
    public static final HTML$Attribute STANDBY = new HTML$Attribute("standby");
    public static final HTML$Attribute BORDER = new HTML$Attribute("border");
    public static final HTML$Attribute SHAPES = new HTML$Attribute("shapes");
    public static final HTML$Attribute NOSHADE = new HTML$Attribute("noshade");
    public static final HTML$Attribute COMPACT = new HTML$Attribute("compact");
    public static final HTML$Attribute START = new HTML$Attribute("start");
    public static final HTML$Attribute ACTION = new HTML$Attribute("action");
    public static final HTML$Attribute METHOD = new HTML$Attribute("method");
    public static final HTML$Attribute ENCTYPE = new HTML$Attribute("enctype");
    public static final HTML$Attribute CHECKED = new HTML$Attribute("checked");
    public static final HTML$Attribute MAXLENGTH = new HTML$Attribute("maxlength");
    public static final HTML$Attribute MULTIPLE = new HTML$Attribute("multiple");
    public static final HTML$Attribute SELECTED = new HTML$Attribute("selected");
    public static final HTML$Attribute ROWS = new HTML$Attribute("rows");
    public static final HTML$Attribute COLS = new HTML$Attribute("cols");
    public static final HTML$Attribute DUMMY = new HTML$Attribute("dummy");
    public static final HTML$Attribute CELLSPACING = new HTML$Attribute("cellspacing");
    public static final HTML$Attribute CELLPADDING = new HTML$Attribute("cellpadding");
    public static final HTML$Attribute VALIGN = new HTML$Attribute("valign");
    public static final HTML$Attribute HALIGN = new HTML$Attribute("halign");
    public static final HTML$Attribute NOWRAP = new HTML$Attribute("nowrap");
    public static final HTML$Attribute ROWSPAN = new HTML$Attribute("rowspan");
    public static final HTML$Attribute COLSPAN = new HTML$Attribute("colspan");
    public static final HTML$Attribute PROMPT = new HTML$Attribute("prompt");
    public static final HTML$Attribute HTTPEQUIV = new HTML$Attribute("http-equiv");
    public static final HTML$Attribute CONTENT = new HTML$Attribute("content");
    public static final HTML$Attribute LANGUAGE = new HTML$Attribute("language");
    public static final HTML$Attribute VERSION = new HTML$Attribute("version");
    public static final HTML$Attribute N = new HTML$Attribute("n");
    public static final HTML$Attribute FRAMEBORDER = new HTML$Attribute("frameborder");
    public static final HTML$Attribute MARGINWIDTH = new HTML$Attribute("marginwidth");
    public static final HTML$Attribute MARGINHEIGHT = new HTML$Attribute("marginheight");
    public static final HTML$Attribute SCROLLING = new HTML$Attribute("scrolling");
    public static final HTML$Attribute NORESIZE = new HTML$Attribute("noresize");
    public static final HTML$Attribute ENDTAG = new HTML$Attribute("endtag");
    public static final HTML$Attribute COMMENT = new HTML$Attribute("comment");
    static final HTML$Attribute MEDIA = new HTML$Attribute("media");
    static final HTML$Attribute[] allAttributes = {FACE, COMMENT, SIZE, COLOR, CLEAR, BACKGROUND, BGCOLOR, TEXT, LINK, VLINK, ALINK, WIDTH, HEIGHT, ALIGN, NAME, HREF, REL, REV, TITLE, TARGET, SHAPE, COORDS, ISMAP, NOHREF, ALT, ID, SRC, HSPACE, VSPACE, USEMAP, LOWSRC, CODEBASE, CODE, ARCHIVE, VALUE, VALUETYPE, TYPE, CLASS, STYLE, LANG, DIR, DECLARE, CLASSID, DATA, CODETYPE, STANDBY, BORDER, SHAPES, NOSHADE, COMPACT, START, ACTION, METHOD, ENCTYPE, CHECKED, MAXLENGTH, MULTIPLE, SELECTED, ROWS, COLS, DUMMY, CELLSPACING, CELLPADDING, VALIGN, HALIGN, NOWRAP, ROWSPAN, COLSPAN, PROMPT, HTTPEQUIV, CONTENT, LANGUAGE, VERSION, N, FRAMEBORDER, MARGINWIDTH, MARGINHEIGHT, SCROLLING, NORESIZE, MEDIA, ENDTAG};
}
