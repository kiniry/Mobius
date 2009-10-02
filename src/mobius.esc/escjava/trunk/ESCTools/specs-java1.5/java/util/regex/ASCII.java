package java.util.regex;

final class ASCII {
    
    ASCII() {
        
    }
    static final int UPPER = 256;
    static final int LOWER = 512;
    static final int DIGIT = 1024;
    static final int SPACE = 2048;
    static final int PUNCT = 4096;
    static final int CNTRL = 8192;
    static final int BLANK = 16384;
    static final int HEX = 32768;
    static final int UNDER = 65536;
    static final int ASCII = 65280;
    static final int ALPHA = (UPPER | LOWER);
    static final int ALNUM = (UPPER | LOWER | DIGIT);
    static final int GRAPH = (PUNCT | UPPER | LOWER | DIGIT);
    static final int WORD = (UPPER | LOWER | UNDER | DIGIT);
    static final int XDIGIT = (HEX);
    private static final int[] ctype = new int[]{CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, SPACE + CNTRL + BLANK, SPACE + CNTRL, SPACE + CNTRL, SPACE + CNTRL, SPACE + CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, CNTRL, SPACE + BLANK, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, DIGIT + HEX + 0, DIGIT + HEX + 1, DIGIT + HEX + 2, DIGIT + HEX + 3, DIGIT + HEX + 4, DIGIT + HEX + 5, DIGIT + HEX + 6, DIGIT + HEX + 7, DIGIT + HEX + 8, DIGIT + HEX + 9, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT, UPPER + HEX + 10, UPPER + HEX + 11, UPPER + HEX + 12, UPPER + HEX + 13, UPPER + HEX + 14, UPPER + HEX + 15, UPPER + 16, UPPER + 17, UPPER + 18, UPPER + 19, UPPER + 20, UPPER + 21, UPPER + 22, UPPER + 23, UPPER + 24, UPPER + 25, UPPER + 26, UPPER + 27, UPPER + 28, UPPER + 29, UPPER + 30, UPPER + 31, UPPER + 32, UPPER + 33, UPPER + 34, UPPER + 35, PUNCT, PUNCT, PUNCT, PUNCT, PUNCT | UNDER, PUNCT, LOWER + HEX + 10, LOWER + HEX + 11, LOWER + HEX + 12, LOWER + HEX + 13, LOWER + HEX + 14, LOWER + HEX + 15, LOWER + 16, LOWER + 17, LOWER + 18, LOWER + 19, LOWER + 20, LOWER + 21, LOWER + 22, LOWER + 23, LOWER + 24, LOWER + 25, LOWER + 26, LOWER + 27, LOWER + 28, LOWER + 29, LOWER + 30, LOWER + 31, LOWER + 32, LOWER + 33, LOWER + 34, LOWER + 35, PUNCT, PUNCT, PUNCT, PUNCT, CNTRL};
    
    static int getType(int ch) {
        return ((ch & -128) == 0 ? ctype[ch] : 0);
    }
    
    static boolean isType(int ch, int type) {
        return (getType(ch) & type) != 0;
    }
    
    static boolean isAscii(int ch) {
        return ((ch & -128) == 0);
    }
    
    static boolean isAlpha(int ch) {
        return isType(ch, ALPHA);
    }
    
    static boolean isDigit(int ch) {
        return ((ch - '0') | ('9' - ch)) >= 0;
    }
    
    static boolean isAlnum(int ch) {
        return isType(ch, ALNUM);
    }
    
    static boolean isGraph(int ch) {
        return isType(ch, GRAPH);
    }
    
    static boolean isPrint(int ch) {
        return ((ch - 32) | (126 - ch)) >= 0;
    }
    
    static boolean isPunct(int ch) {
        return isType(ch, PUNCT);
    }
    
    static boolean isSpace(int ch) {
        return isType(ch, SPACE);
    }
    
    static boolean isHexDigit(int ch) {
        return isType(ch, HEX);
    }
    
    static boolean isOctDigit(int ch) {
        return ((ch - '0') | ('7' - ch)) >= 0;
    }
    
    static boolean isCntrl(int ch) {
        return isType(ch, CNTRL);
    }
    
    static boolean isLower(int ch) {
        return ((ch - 'a') | ('z' - ch)) >= 0;
    }
    
    static boolean isUpper(int ch) {
        return ((ch - 'A') | ('Z' - ch)) >= 0;
    }
    
    static boolean isWord(int ch) {
        return isType(ch, WORD);
    }
    
    static int toDigit(int ch) {
        return (ctype[ch & 127] & 63);
    }
    
    static int toLower(int ch) {
        return isUpper(ch) ? (ch + 32) : ch;
    }
    
    static int toUpper(int ch) {
        return isLower(ch) ? (ch - 32) : ch;
    }
}
