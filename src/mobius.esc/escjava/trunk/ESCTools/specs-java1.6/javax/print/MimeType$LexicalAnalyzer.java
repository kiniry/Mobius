package javax.print;

class MimeType$LexicalAnalyzer {
    protected String mySource;
    protected int mySourceLength;
    protected int myCurrentIndex;
    protected int myLexemeType;
    protected int myLexemeBeginIndex;
    protected int myLexemeEndIndex;
    
    public MimeType$LexicalAnalyzer(String theSource) {
        
        mySource = theSource;
        mySourceLength = theSource.length();
        myCurrentIndex = 0;
        nextLexeme();
    }
    
    public int getLexemeType() {
        return myLexemeType;
    }
    
    public String getLexeme() {
        return (myLexemeBeginIndex >= mySourceLength ? null : mySource.substring(myLexemeBeginIndex, myLexemeEndIndex));
    }
    
    public char getLexemeFirstCharacter() {
        return (myLexemeBeginIndex >= mySourceLength ? '\000' : mySource.charAt(myLexemeBeginIndex));
    }
    
    public void nextLexeme() {
        int state = 0;
        int commentLevel = 0;
        char c;
        while (state >= 0) {
            switch (state) {
            case 0: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeType = 3;
                    myLexemeBeginIndex = mySourceLength;
                    myLexemeEndIndex = mySourceLength;
                    state = -1;
                } else if (Character.isWhitespace(c = mySource.charAt(myCurrentIndex++))) {
                    state = 0;
                } else if (c == '\"') {
                    myLexemeType = 1;
                    myLexemeBeginIndex = myCurrentIndex;
                    state = 1;
                } else if (c == '(') {
                    ++commentLevel;
                    state = 3;
                } else if (c == '/' || c == ';' || c == '=' || c == ')' || c == '<' || c == '>' || c == '@' || c == ',' || c == ':' || c == '\\' || c == '[' || c == ']' || c == '?') {
                    myLexemeType = 2;
                    myLexemeBeginIndex = myCurrentIndex - 1;
                    myLexemeEndIndex = myCurrentIndex;
                    state = -1;
                } else {
                    myLexemeType = 0;
                    myLexemeBeginIndex = myCurrentIndex - 1;
                    state = 5;
                }
                break;
            
            case 1: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeType = 4;
                    myLexemeBeginIndex = mySourceLength;
                    myLexemeEndIndex = mySourceLength;
                    state = -1;
                } else if ((c = mySource.charAt(myCurrentIndex++)) == '\"') {
                    myLexemeEndIndex = myCurrentIndex - 1;
                    state = -1;
                } else if (c == '\\') {
                    state = 2;
                } else {
                    state = 1;
                }
                break;
            
            case 2: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeType = 4;
                    myLexemeBeginIndex = mySourceLength;
                    myLexemeEndIndex = mySourceLength;
                    state = -1;
                } else {
                    ++myCurrentIndex;
                    state = 1;
                }
                break;
            
            case 3: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeType = 4;
                    myLexemeBeginIndex = mySourceLength;
                    myLexemeEndIndex = mySourceLength;
                    state = -1;
                } else if ((c = mySource.charAt(myCurrentIndex++)) == '(') {
                    ++commentLevel;
                    state = 3;
                } else if (c == ')') {
                    --commentLevel;
                    state = commentLevel == 0 ? 0 : 3;
                } else if (c == '\\') {
                    state = 4;
                } else {
                    state = 3;
                }
                break;
            
            case 4: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeType = 4;
                    myLexemeBeginIndex = mySourceLength;
                    myLexemeEndIndex = mySourceLength;
                    state = -1;
                } else {
                    ++myCurrentIndex;
                    state = 3;
                }
                break;
            
            case 5: 
                if (myCurrentIndex >= mySourceLength) {
                    myLexemeEndIndex = myCurrentIndex;
                    state = -1;
                } else if (Character.isWhitespace(c = mySource.charAt(myCurrentIndex++))) {
                    myLexemeEndIndex = myCurrentIndex - 1;
                    state = -1;
                } else if (c == '\"' || c == '(' || c == '/' || c == ';' || c == '=' || c == ')' || c == '<' || c == '>' || c == '@' || c == ',' || c == ':' || c == '\\' || c == '[' || c == ']' || c == '?') {
                    --myCurrentIndex;
                    myLexemeEndIndex = myCurrentIndex;
                    state = -1;
                } else {
                    state = 5;
                }
                break;
            
            }
        }
    }
}
