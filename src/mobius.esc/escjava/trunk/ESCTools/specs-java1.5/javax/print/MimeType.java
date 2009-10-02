package javax.print;

import java.io.Serializable;
import java.util.Map;
import java.util.Vector;

class MimeType implements Serializable, Cloneable {
    
    /*synthetic*/ static MimeType$ParameterMapEntrySet access$202(MimeType x0, MimeType$ParameterMapEntrySet x1) {
        return x0.myEntrySet = x1;
    }
    
    /*synthetic*/ static MimeType$ParameterMapEntrySet access$200(MimeType x0) {
        return x0.myEntrySet;
    }
    
    /*synthetic*/ static String[] access$000(MimeType x0) {
        return x0.myPieces;
    }
    {
    }
    private static final long serialVersionUID = -2785720609362367683L;
    private String[] myPieces;
    private transient String myStringValue = null;
    private transient MimeType$ParameterMapEntrySet myEntrySet = null;
    private transient MimeType$ParameterMap myParameterMap = null;
    {
    }
    {
    }
    {
    }
    {
    }
    
    public MimeType(String s) {
        
        parse(s);
    }
    
    public String getMimeType() {
        return getStringValue();
    }
    
    public String getMediaType() {
        return myPieces[0];
    }
    
    public String getMediaSubtype() {
        return myPieces[1];
    }
    
    public Map getParameterMap() {
        if (myParameterMap == null) {
            myParameterMap = new MimeType$ParameterMap(this, null);
        }
        return myParameterMap;
    }
    
    public String toString() {
        return getStringValue();
    }
    
    public int hashCode() {
        return getStringValue().hashCode();
    }
    
    public boolean equals(Object obj) {
        return (obj != null && obj instanceof MimeType && getStringValue().equals(((MimeType)(MimeType)obj).getStringValue()));
    }
    
    private String getStringValue() {
        if (myStringValue == null) {
            StringBuffer result = new StringBuffer();
            result.append(myPieces[0]);
            result.append('/');
            result.append(myPieces[1]);
            int n = myPieces.length;
            for (int i = 2; i < n; i += 2) {
                result.append(';');
                result.append(' ');
                result.append(myPieces[i]);
                result.append('=');
                result.append(addQuotes(myPieces[i + 1]));
            }
            myStringValue = result.toString();
        }
        return myStringValue;
    }
    private static final int TOKEN_LEXEME = 0;
    private static final int QUOTED_STRING_LEXEME = 1;
    private static final int TSPECIAL_LEXEME = 2;
    private static final int EOF_LEXEME = 3;
    private static final int ILLEGAL_LEXEME = 4;
    {
    }
    
    private static String toUnicodeLowerCase(String s) {
        int n = s.length();
        char[] result = new char[n];
        for (int i = 0; i < n; ++i) {
            result[i] = Character.toLowerCase(s.charAt(i));
        }
        return new String(result);
    }
    
    private static String removeBackslashes(String s) {
        int n = s.length();
        char[] result = new char[n];
        int i;
        int j = 0;
        char c;
        for (i = 0; i < n; ++i) {
            c = s.charAt(i);
            if (c == '\\') {
                c = s.charAt(++i);
            }
            result[j++] = c;
        }
        return new String(result, 0, j);
    }
    
    private static String addQuotes(String s) {
        int n = s.length();
        int i;
        char c;
        StringBuffer result = new StringBuffer(n + 2);
        result.append('\"');
        for (i = 0; i < n; ++i) {
            c = s.charAt(i);
            if (c == '\"') {
                result.append('\\');
            }
            result.append(c);
        }
        result.append('\"');
        return result.toString();
    }
    
    private void parse(String s) {
        if (s == null) {
            throw new NullPointerException();
        }
        MimeType$LexicalAnalyzer theLexer = new MimeType$LexicalAnalyzer(s);
        int theLexemeType;
        Vector thePieces = new Vector();
        boolean mediaTypeIsText = false;
        boolean parameterNameIsCharset = false;
        if (theLexer.getLexemeType() == TOKEN_LEXEME) {
            String mt = toUnicodeLowerCase(theLexer.getLexeme());
            thePieces.add(mt);
            theLexer.nextLexeme();
            mediaTypeIsText = mt.equals("text");
        } else {
            throw new IllegalArgumentException();
        }
        if (theLexer.getLexemeType() == TSPECIAL_LEXEME && theLexer.getLexemeFirstCharacter() == '/') {
            theLexer.nextLexeme();
        } else {
            throw new IllegalArgumentException();
        }
        if (theLexer.getLexemeType() == TOKEN_LEXEME) {
            thePieces.add(toUnicodeLowerCase(theLexer.getLexeme()));
            theLexer.nextLexeme();
        } else {
            throw new IllegalArgumentException();
        }
        while (theLexer.getLexemeType() == TSPECIAL_LEXEME && theLexer.getLexemeFirstCharacter() == ';') {
            theLexer.nextLexeme();
            if (theLexer.getLexemeType() == TOKEN_LEXEME) {
                String pn = toUnicodeLowerCase(theLexer.getLexeme());
                thePieces.add(pn);
                theLexer.nextLexeme();
                parameterNameIsCharset = pn.equals("charset");
            } else {
                throw new IllegalArgumentException();
            }
            if (theLexer.getLexemeType() == TSPECIAL_LEXEME && theLexer.getLexemeFirstCharacter() == '=') {
                theLexer.nextLexeme();
            } else {
                throw new IllegalArgumentException();
            }
            if (theLexer.getLexemeType() == TOKEN_LEXEME) {
                String pv = theLexer.getLexeme();
                thePieces.add(mediaTypeIsText && parameterNameIsCharset ? toUnicodeLowerCase(pv) : pv);
                theLexer.nextLexeme();
            } else if (theLexer.getLexemeType() == QUOTED_STRING_LEXEME) {
                String pv = removeBackslashes(theLexer.getLexeme());
                thePieces.add(mediaTypeIsText && parameterNameIsCharset ? toUnicodeLowerCase(pv) : pv);
                theLexer.nextLexeme();
            } else {
                throw new IllegalArgumentException();
            }
        }
        if (theLexer.getLexemeType() != EOF_LEXEME) {
            throw new IllegalArgumentException();
        }
        int n = thePieces.size();
        myPieces = (String[])(String[])thePieces.toArray(new String[n]);
        int i;
        int j;
        String temp;
        for (i = 4; i < n; i += 2) {
            j = 2;
            while (j < i && myPieces[j].compareTo(myPieces[i]) <= 0) {
                j += 2;
            }
            while (j < i) {
                temp = myPieces[j];
                myPieces[j] = myPieces[i];
                myPieces[i] = temp;
                temp = myPieces[j + 1];
                myPieces[j + 1] = myPieces[i + 1];
                myPieces[i + 1] = temp;
                j += 2;
            }
        }
    }
}
