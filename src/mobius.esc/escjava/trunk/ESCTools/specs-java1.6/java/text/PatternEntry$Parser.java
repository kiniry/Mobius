package java.text;

class PatternEntry$Parser {
    private String pattern;
    private int i;
    
    public PatternEntry$Parser(String pattern) {
        
        this.pattern = pattern;
        this.i = 0;
    }
    
    public PatternEntry next() throws ParseException {
        int newStrength = -1;
        newChars.setLength(0);
        newExtension.setLength(0);
        boolean inChars = true;
        boolean inQuote = false;
        mainLoop: while (i < pattern.length()) {
            char ch = pattern.charAt(i);
            if (inQuote) {
                if (ch == '\'') {
                    inQuote = false;
                } else {
                    if (newChars.length() == 0) newChars.append(ch); else if (inChars) newChars.append(ch); else newExtension.append(ch);
                }
            } else switch (ch) {
            case '=': 
                if (newStrength != -1) break mainLoop;
                newStrength = Collator.IDENTICAL;
                break;
            
            case ',': 
                if (newStrength != -1) break mainLoop;
                newStrength = Collator.TERTIARY;
                break;
            
            case ';': 
                if (newStrength != -1) break mainLoop;
                newStrength = Collator.SECONDARY;
                break;
            
            case '<': 
                if (newStrength != -1) break mainLoop;
                newStrength = Collator.PRIMARY;
                break;
            
            case '&': 
                if (newStrength != -1) break mainLoop;
                newStrength = -2;
                break;
            
            case '\t': 
            
            case '\n': 
            
            case '\f': 
            
            case '\r': 
            
            case ' ': 
                break;
            
            case '/': 
                inChars = false;
                break;
            
            case '\'': 
                inQuote = true;
                ch = pattern.charAt(++i);
                if (newChars.length() == 0) newChars.append(ch); else if (inChars) newChars.append(ch); else newExtension.append(ch);
                break;
            
            default: 
                if (newStrength == -1) {
                    throw new ParseException("missing char (=,;<&) : " + pattern.substring(i, (i + 10 < pattern.length()) ? i + 10 : pattern.length()), i);
                }
                if (PatternEntry.isSpecialChar(ch) && (inQuote == false)) throw new ParseException("Unquoted punctuation character : " + Integer.toString(ch, 16), i);
                if (inChars) {
                    newChars.append(ch);
                } else {
                    newExtension.append(ch);
                }
                break;
            
            }
            i++;
        }
        if (newStrength == -1) return null;
        if (newChars.length() == 0) {
            throw new ParseException("missing chars (=,;<&): " + pattern.substring(i, (i + 10 < pattern.length()) ? i + 10 : pattern.length()), i);
        }
        return new PatternEntry(newStrength, newChars, newExtension);
    }
    private StringBuffer newChars = new StringBuffer();
    private StringBuffer newExtension = new StringBuffer();
}
