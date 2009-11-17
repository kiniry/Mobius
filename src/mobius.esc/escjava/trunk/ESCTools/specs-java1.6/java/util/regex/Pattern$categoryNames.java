package java.util.regex;

import java.util.HashMap;

class Pattern$categoryNames {
    
    Pattern$categoryNames() {
        
    }
    static HashMap cMap = new HashMap();
    static {
        cMap.put("Cn", new Pattern$Category(1 << 0));
        cMap.put("Lu", new Pattern$Category(1 << 1));
        cMap.put("Ll", new Pattern$Category(1 << 2));
        cMap.put("Lt", new Pattern$Category(1 << 3));
        cMap.put("Lm", new Pattern$Category(1 << 4));
        cMap.put("Lo", new Pattern$Category(1 << 5));
        cMap.put("Mn", new Pattern$Category(1 << 6));
        cMap.put("Me", new Pattern$Category(1 << 7));
        cMap.put("Mc", new Pattern$Category(1 << 8));
        cMap.put("Nd", new Pattern$Category(1 << 9));
        cMap.put("Nl", new Pattern$Category(1 << 10));
        cMap.put("No", new Pattern$Category(1 << 11));
        cMap.put("Zs", new Pattern$Category(1 << 12));
        cMap.put("Zl", new Pattern$Category(1 << 13));
        cMap.put("Zp", new Pattern$Category(1 << 14));
        cMap.put("Cc", new Pattern$Category(1 << 15));
        cMap.put("Cf", new Pattern$Category(1 << 16));
        cMap.put("Co", new Pattern$Category(1 << 18));
        cMap.put("Cs", new Pattern$Category(1 << 19));
        cMap.put("Pd", new Pattern$Category(1 << 20));
        cMap.put("Ps", new Pattern$Category(1 << 21));
        cMap.put("Pe", new Pattern$Category(1 << 22));
        cMap.put("Pc", new Pattern$Category(1 << 23));
        cMap.put("Po", new Pattern$Category(1 << 24));
        cMap.put("Sm", new Pattern$Category(1 << 25));
        cMap.put("Sc", new Pattern$Category(1 << 26));
        cMap.put("Sk", new Pattern$Category(1 << 27));
        cMap.put("So", new Pattern$Category(1 << 28));
        cMap.put("L", new Pattern$Category(62));
        cMap.put("M", new Pattern$Category(448));
        cMap.put("N", new Pattern$Category(3584));
        cMap.put("Z", new Pattern$Category(28672));
        cMap.put("C", new Pattern$Category(884736));
        cMap.put("P", new Pattern$Category(32505856));
        cMap.put("S", new Pattern$Category(503316480));
        cMap.put("LD", new Pattern$Category(574));
        cMap.put("L1", new Pattern$Range(255));
        cMap.put("all", new Pattern$All());
        cMap.put("ASCII", new Pattern$Range(127));
        cMap.put("Alnum", new Pattern$Ctype(ASCII.ALNUM));
        cMap.put("Alpha", new Pattern$Ctype(ASCII.ALPHA));
        cMap.put("Blank", new Pattern$Ctype(ASCII.BLANK));
        cMap.put("Cntrl", new Pattern$Ctype(ASCII.CNTRL));
        cMap.put("Digit", new Pattern$Range(('0' << 16) | '9'));
        cMap.put("Graph", new Pattern$Ctype(ASCII.GRAPH));
        cMap.put("Lower", new Pattern$Range(('a' << 16) | 'z'));
        cMap.put("Print", new Pattern$Range(2097278));
        cMap.put("Punct", new Pattern$Ctype(ASCII.PUNCT));
        cMap.put("Space", new Pattern$Ctype(ASCII.SPACE));
        cMap.put("Upper", new Pattern$Range(('A' << 16) | 'Z'));
        cMap.put("XDigit", new Pattern$Ctype(ASCII.XDIGIT));
        cMap.put("javaLowerCase", new Pattern$JavaLowerCase());
        cMap.put("javaUpperCase", new Pattern$JavaUpperCase());
        cMap.put("javaTitleCase", new Pattern$JavaTitleCase());
        cMap.put("javaDigit", new Pattern$JavaDigit());
        cMap.put("javaDefined", new Pattern$JavaDefined());
        cMap.put("javaLetter", new Pattern$JavaLetter());
        cMap.put("javaLetterOrDigit", new Pattern$JavaLetterOrDigit());
        cMap.put("javaJavaIdentifierStart", new Pattern$JavaJavaIdentifierStart());
        cMap.put("javaJavaIdentifierPart", new Pattern$JavaJavaIdentifierPart());
        cMap.put("javaUnicodeIdentifierStart", new Pattern$JavaUnicodeIdentifierStart());
        cMap.put("javaUnicodeIdentifierPart", new Pattern$JavaUnicodeIdentifierPart());
        cMap.put("javaIdentifierIgnorable", new Pattern$JavaIdentifierIgnorable());
        cMap.put("javaSpaceChar", new Pattern$JavaSpaceChar());
        cMap.put("javaWhitespace", new Pattern$JavaWhitespace());
        cMap.put("javaISOControl", new Pattern$JavaISOControl());
        cMap.put("javaMirrored", new Pattern$JavaMirrored());
    }
}
