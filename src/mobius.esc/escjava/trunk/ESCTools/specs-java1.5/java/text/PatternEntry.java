package java.text;

import java.lang.Character;

class PatternEntry {
    
    public void appendQuotedExtension(StringBuffer toAddTo) {
        appendQuoted(extension, toAddTo);
    }
    
    public void appendQuotedChars(StringBuffer toAddTo) {
        appendQuoted(chars, toAddTo);
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        PatternEntry other = (PatternEntry)(PatternEntry)obj;
        boolean result = chars.equals(other.chars);
        return result;
    }
    
    public int hashCode() {
        return chars.hashCode();
    }
    
    public String toString() {
        StringBuffer result = new StringBuffer();
        addToBuffer(result, true, false, null);
        return result.toString();
    }
    
    final int getStrength() {
        return strength;
    }
    
    final String getExtension() {
        return extension;
    }
    
    final String getChars() {
        return chars;
    }
    
    void addToBuffer(StringBuffer toAddTo, boolean showExtension, boolean showWhiteSpace, PatternEntry lastEntry) {
        if (showWhiteSpace && toAddTo.length() > 0) if (strength == Collator.PRIMARY || lastEntry != null) toAddTo.append('\n'); else toAddTo.append(' ');
        if (lastEntry != null) {
            toAddTo.append('&');
            if (showWhiteSpace) toAddTo.append(' ');
            lastEntry.appendQuotedChars(toAddTo);
            appendQuotedExtension(toAddTo);
            if (showWhiteSpace) toAddTo.append(' ');
        }
        switch (strength) {
        case Collator.IDENTICAL: 
            toAddTo.append('=');
            break;
        
        case Collator.TERTIARY: 
            toAddTo.append(',');
            break;
        
        case Collator.SECONDARY: 
            toAddTo.append(';');
            break;
        
        case Collator.PRIMARY: 
            toAddTo.append('<');
            break;
        
        case RESET: 
            toAddTo.append('&');
            break;
        
        case UNSET: 
            toAddTo.append('?');
            break;
        
        }
        if (showWhiteSpace) toAddTo.append(' ');
        appendQuoted(chars, toAddTo);
        if (showExtension && extension.length() != 0) {
            toAddTo.append('/');
            appendQuoted(extension, toAddTo);
        }
    }
    
    static void appendQuoted(String chars, StringBuffer toAddTo) {
        boolean inQuote = false;
        char ch = chars.charAt(0);
        if (Character.isSpaceChar(ch)) {
            inQuote = true;
            toAddTo.append('\'');
        } else {
            if (PatternEntry.isSpecialChar(ch)) {
                inQuote = true;
                toAddTo.append('\'');
            } else {
                switch (ch) {
                case 16: 
                
                case '\f': 
                
                case '\r': 
                
                case '\t': 
                
                case '\n': 
                
                case '@': 
                    inQuote = true;
                    toAddTo.append('\'');
                    break;
                
                case '\'': 
                    inQuote = true;
                    toAddTo.append('\'');
                    break;
                
                default: 
                    if (inQuote) {
                        inQuote = false;
                        toAddTo.append('\'');
                    }
                    break;
                
                }
            }
        }
        toAddTo.append(chars);
        if (inQuote) toAddTo.append('\'');
    }
    
    PatternEntry(int strength, StringBuffer chars, StringBuffer extension) {
        
        this.strength = strength;
        this.chars = chars.toString();
        this.extension = (extension.length() > 0) ? extension.toString() : "";
    }
    {
    }
    
    static boolean isSpecialChar(char ch) {
        return ((ch == ' ') || ((ch <= '/') && (ch >= '\"')) || ((ch <= '?') && (ch >= ':')) || ((ch <= '`') && (ch >= '[')) || ((ch <= '~') && (ch >= '{')));
    }
    static final int RESET = -2;
    static final int UNSET = -1;
    int strength = UNSET;
    String chars = "";
    String extension = "";
}
