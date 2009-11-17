package javax.swing.text.html;

import java.io.*;

class CSSParser {
    private static final int IDENTIFIER = 1;
    private static final int BRACKET_OPEN = 2;
    private static final int BRACKET_CLOSE = 3;
    private static final int BRACE_OPEN = 4;
    private static final int BRACE_CLOSE = 5;
    private static final int PAREN_OPEN = 6;
    private static final int PAREN_CLOSE = 7;
    private static final int END = -1;
    private static final char[] charMapping = {0, 0, '[', ']', '{', '}', '(', ')', 0};
    private boolean didPushChar;
    private int pushedChar;
    private StringBuffer unitBuffer;
    private int[] unitStack;
    private int stackCount;
    private Reader reader;
    private boolean encounteredRuleSet;
    private CSSParser$CSSParserCallback callback;
    private char[] tokenBuffer;
    private int tokenBufferLength;
    private boolean readWS;
    {
    }
    
    CSSParser() {
        
        unitStack = new int[2];
        tokenBuffer = new char[80];
        unitBuffer = new StringBuffer();
    }
    
    void parse(Reader reader, CSSParser$CSSParserCallback callback, boolean inRule) throws IOException {
        this.callback = callback;
        stackCount = tokenBufferLength = 0;
        this.reader = reader;
        encounteredRuleSet = false;
        try {
            if (inRule) {
                parseDeclarationBlock();
            } else {
                while (getNextStatement()) ;
            }
        } finally {
            callback = null;
            reader = null;
        }
    }
    
    private boolean getNextStatement() throws IOException {
        unitBuffer.setLength(0);
        int token = nextToken((char)0);
        switch (token) {
        case IDENTIFIER: 
            if (tokenBufferLength > 0) {
                if (tokenBuffer[0] == '@') {
                    parseAtRule();
                } else {
                    encounteredRuleSet = true;
                    parseRuleSet();
                }
            }
            return true;
        
        case BRACKET_OPEN: 
        
        case BRACE_OPEN: 
        
        case PAREN_OPEN: 
            parseTillClosed(token);
            return true;
        
        case BRACKET_CLOSE: 
        
        case BRACE_CLOSE: 
        
        case PAREN_CLOSE: 
            throw new RuntimeException("Unexpected top level block close");
        
        case END: 
            return false;
        
        }
        return true;
    }
    
    private void parseAtRule() throws IOException {
        boolean done = false;
        boolean isImport = (tokenBufferLength == 7 && tokenBuffer[0] == '@' && tokenBuffer[1] == 'i' && tokenBuffer[2] == 'm' && tokenBuffer[3] == 'p' && tokenBuffer[4] == 'o' && tokenBuffer[5] == 'r' && tokenBuffer[6] == 't');
        unitBuffer.setLength(0);
        while (!done) {
            int nextToken = nextToken(';');
            switch (nextToken) {
            case IDENTIFIER: 
                if (tokenBufferLength > 0 && tokenBuffer[tokenBufferLength - 1] == ';') {
                    --tokenBufferLength;
                    done = true;
                }
                if (tokenBufferLength > 0) {
                    if (unitBuffer.length() > 0 && readWS) {
                        unitBuffer.append(' ');
                    }
                    unitBuffer.append(tokenBuffer, 0, tokenBufferLength);
                }
                break;
            
            case BRACE_OPEN: 
                if (unitBuffer.length() > 0 && readWS) {
                    unitBuffer.append(' ');
                }
                unitBuffer.append(charMapping[nextToken]);
                parseTillClosed(nextToken);
                done = true;
                {
                    int nextChar = readWS();
                    if (nextChar != -1 && nextChar != ';') {
                        pushChar(nextChar);
                    }
                }
                break;
            
            case BRACKET_OPEN: 
            
            case PAREN_OPEN: 
                unitBuffer.append(charMapping[nextToken]);
                parseTillClosed(nextToken);
                break;
            
            case BRACKET_CLOSE: 
            
            case BRACE_CLOSE: 
            
            case PAREN_CLOSE: 
                throw new RuntimeException("Unexpected close in @ rule");
            
            case END: 
                done = true;
                break;
            
            }
        }
        if (isImport && !encounteredRuleSet) {
            callback.handleImport(unitBuffer.toString());
        }
    }
    
    private void parseRuleSet() throws IOException {
        if (parseSelectors()) {
            callback.startRule();
            parseDeclarationBlock();
            callback.endRule();
        }
    }
    
    private boolean parseSelectors() throws IOException {
        int nextToken;
        if (tokenBufferLength > 0) {
            callback.handleSelector(new String(tokenBuffer, 0, tokenBufferLength));
        }
        unitBuffer.setLength(0);
        for (; ; ) {
            while ((nextToken = nextToken((char)0)) == IDENTIFIER) {
                if (tokenBufferLength > 0) {
                    callback.handleSelector(new String(tokenBuffer, 0, tokenBufferLength));
                }
            }
            switch (nextToken) {
            case BRACE_OPEN: 
                return true;
            
            case BRACKET_OPEN: 
            
            case PAREN_OPEN: 
                parseTillClosed(nextToken);
                unitBuffer.setLength(0);
                break;
            
            case BRACKET_CLOSE: 
            
            case BRACE_CLOSE: 
            
            case PAREN_CLOSE: 
                throw new RuntimeException("Unexpected block close in selector");
            
            case END: 
                return false;
            
            }
        }
    }
    
    private void parseDeclarationBlock() throws IOException {
        for (; ; ) {
            int token = parseDeclaration();
            switch (token) {
            case END: 
            
            case BRACE_CLOSE: 
                return;
            
            case BRACKET_CLOSE: 
            
            case PAREN_CLOSE: 
                throw new RuntimeException("Unexpected close in declaration block");
            
            case IDENTIFIER: 
                break;
            
            }
        }
    }
    
    private int parseDeclaration() throws IOException {
        int token;
        if ((token = parseIdentifiers(':', false)) != IDENTIFIER) {
            return token;
        }
        for (int counter = unitBuffer.length() - 1; counter >= 0; counter--) {
            unitBuffer.setCharAt(counter, Character.toLowerCase(unitBuffer.charAt(counter)));
        }
        callback.handleProperty(unitBuffer.toString());
        token = parseIdentifiers(';', true);
        callback.handleValue(unitBuffer.toString());
        return token;
    }
    
    private int parseIdentifiers(char extraChar, boolean wantsBlocks) throws IOException {
        int nextToken;
        int ubl;
        unitBuffer.setLength(0);
        for (; ; ) {
            nextToken = nextToken(extraChar);
            switch (nextToken) {
            case IDENTIFIER: 
                if (tokenBufferLength > 0) {
                    if (tokenBuffer[tokenBufferLength - 1] == extraChar) {
                        if (--tokenBufferLength > 0) {
                            if (readWS && unitBuffer.length() > 0) {
                                unitBuffer.append(' ');
                            }
                            unitBuffer.append(tokenBuffer, 0, tokenBufferLength);
                        }
                        return IDENTIFIER;
                    }
                    if (readWS && unitBuffer.length() > 0) {
                        unitBuffer.append(' ');
                    }
                    unitBuffer.append(tokenBuffer, 0, tokenBufferLength);
                }
                break;
            
            case BRACKET_OPEN: 
            
            case BRACE_OPEN: 
            
            case PAREN_OPEN: 
                ubl = unitBuffer.length();
                if (wantsBlocks) {
                    unitBuffer.append(charMapping[nextToken]);
                }
                parseTillClosed(nextToken);
                if (!wantsBlocks) {
                    unitBuffer.setLength(ubl);
                }
                break;
            
            case BRACE_CLOSE: 
            
            case BRACKET_CLOSE: 
            
            case PAREN_CLOSE: 
            
            case END: 
                return nextToken;
            
            }
        }
    }
    
    private void parseTillClosed(int openToken) throws IOException {
        int nextToken;
        boolean done = false;
        startBlock(openToken);
        while (!done) {
            nextToken = nextToken((char)0);
            switch (nextToken) {
            case IDENTIFIER: 
                if (unitBuffer.length() > 0 && readWS) {
                    unitBuffer.append(' ');
                }
                if (tokenBufferLength > 0) {
                    unitBuffer.append(tokenBuffer, 0, tokenBufferLength);
                }
                break;
            
            case BRACKET_OPEN: 
            
            case BRACE_OPEN: 
            
            case PAREN_OPEN: 
                if (unitBuffer.length() > 0 && readWS) {
                    unitBuffer.append(' ');
                }
                unitBuffer.append(charMapping[nextToken]);
                startBlock(nextToken);
                break;
            
            case BRACKET_CLOSE: 
            
            case BRACE_CLOSE: 
            
            case PAREN_CLOSE: 
                if (unitBuffer.length() > 0 && readWS) {
                    unitBuffer.append(' ');
                }
                unitBuffer.append(charMapping[nextToken]);
                endBlock(nextToken);
                if (!inBlock()) {
                    done = true;
                }
                break;
            
            case END: 
                throw new RuntimeException("Unclosed block");
            
            }
        }
    }
    
    private int nextToken(char idChar) throws IOException {
        readWS = false;
        int nextChar = readWS();
        switch (nextChar) {
        case '\'': 
            readTill('\'');
            if (tokenBufferLength > 0) {
                tokenBufferLength--;
            }
            return IDENTIFIER;
        
        case '\"': 
            readTill('\"');
            if (tokenBufferLength > 0) {
                tokenBufferLength--;
            }
            return IDENTIFIER;
        
        case '[': 
            return BRACKET_OPEN;
        
        case ']': 
            return BRACKET_CLOSE;
        
        case '{': 
            return BRACE_OPEN;
        
        case '}': 
            return BRACE_CLOSE;
        
        case '(': 
            return PAREN_OPEN;
        
        case ')': 
            return PAREN_CLOSE;
        
        case -1: 
            return END;
        
        default: 
            pushChar(nextChar);
            getIdentifier(idChar);
            return IDENTIFIER;
        
        }
    }
    
    private boolean getIdentifier(char stopChar) throws IOException {
        boolean lastWasEscape = false;
        boolean done = false;
        int escapeCount = 0;
        int escapeChar = 0;
        int nextChar;
        int intStopChar = (int)stopChar;
        short type;
        int escapeOffset = 0;
        tokenBufferLength = 0;
        while (!done) {
            nextChar = readChar();
            switch (nextChar) {
            case '\\': 
                type = 1;
                break;
            
            case '0': 
            
            case '1': 
            
            case '2': 
            
            case '3': 
            
            case '4': 
            
            case '5': 
            
            case '6': 
            
            case '7': 
            
            case '8': 
            
            case '9': 
                type = 2;
                escapeOffset = nextChar - '0';
                break;
            
            case 'a': 
            
            case 'b': 
            
            case 'c': 
            
            case 'd': 
            
            case 'e': 
            
            case 'f': 
                type = 2;
                escapeOffset = nextChar - 'a' + 10;
                break;
            
            case 'A': 
            
            case 'B': 
            
            case 'C': 
            
            case 'D': 
            
            case 'E': 
            
            case 'F': 
                type = 2;
                escapeOffset = nextChar - 'A' + 10;
                break;
            
            case '\'': 
            
            case '\"': 
            
            case '[': 
            
            case ']': 
            
            case '{': 
            
            case '}': 
            
            case '(': 
            
            case ')': 
            
            case ' ': 
            
            case '\n': 
            
            case '\t': 
            
            case '\r': 
                type = 3;
                break;
            
            case '/': 
                type = 4;
                break;
            
            case -1: 
                done = true;
                type = 0;
                break;
            
            default: 
                type = 0;
                break;
            
            }
            if (lastWasEscape) {
                if (type == 2) {
                    escapeChar = escapeChar * 16 + escapeOffset;
                    if (++escapeCount == 4) {
                        lastWasEscape = false;
                        append((char)escapeChar);
                    }
                } else {
                    lastWasEscape = false;
                    if (escapeCount > 0) {
                        append((char)escapeChar);
                        pushChar(nextChar);
                    } else if (!done) {
                        append((char)nextChar);
                    }
                }
            } else if (!done) {
                if (type == 1) {
                    lastWasEscape = true;
                    escapeChar = escapeCount = 0;
                } else if (type == 3) {
                    done = true;
                    pushChar(nextChar);
                } else if (type == 4) {
                    nextChar = readChar();
                    if (nextChar == '*') {
                        done = true;
                        readComment();
                        readWS = true;
                    } else {
                        append('/');
                        if (nextChar == -1) {
                            done = true;
                        } else {
                            pushChar(nextChar);
                        }
                    }
                } else {
                    append((char)nextChar);
                    if (nextChar == intStopChar) {
                        done = true;
                    }
                }
            }
        }
        return (tokenBufferLength > 0);
    }
    
    private void readTill(char stopChar) throws IOException {
        boolean lastWasEscape = false;
        int escapeCount = 0;
        int escapeChar = 0;
        int nextChar;
        boolean done = false;
        int intStopChar = (int)stopChar;
        short type;
        int escapeOffset = 0;
        tokenBufferLength = 0;
        while (!done) {
            nextChar = readChar();
            switch (nextChar) {
            case '\\': 
                type = 1;
                break;
            
            case '0': 
            
            case '1': 
            
            case '2': 
            
            case '3': 
            
            case '4': 
            
            case '5': 
            
            case '6': 
            
            case '7': 
            
            case '8': 
            
            case '9': 
                type = 2;
                escapeOffset = nextChar - '0';
                break;
            
            case 'a': 
            
            case 'b': 
            
            case 'c': 
            
            case 'd': 
            
            case 'e': 
            
            case 'f': 
                type = 2;
                escapeOffset = nextChar - 'a' + 10;
                break;
            
            case 'A': 
            
            case 'B': 
            
            case 'C': 
            
            case 'D': 
            
            case 'E': 
            
            case 'F': 
                type = 2;
                escapeOffset = nextChar - 'A' + 10;
                break;
            
            case -1: 
                throw new RuntimeException("Unclosed " + stopChar);
            
            default: 
                type = 0;
                break;
            
            }
            if (lastWasEscape) {
                if (type == 2) {
                    escapeChar = escapeChar * 16 + escapeOffset;
                    if (++escapeCount == 4) {
                        lastWasEscape = false;
                        append((char)escapeChar);
                    }
                } else {
                    if (escapeCount > 0) {
                        append((char)escapeChar);
                        if (type == 1) {
                            lastWasEscape = true;
                            escapeChar = escapeCount = 0;
                        } else {
                            if (nextChar == intStopChar) {
                                done = true;
                            }
                            append((char)nextChar);
                            lastWasEscape = false;
                        }
                    } else {
                        append((char)nextChar);
                        lastWasEscape = false;
                    }
                }
            } else if (type == 1) {
                lastWasEscape = true;
                escapeChar = escapeCount = 0;
            } else {
                if (nextChar == intStopChar) {
                    done = true;
                }
                append((char)nextChar);
            }
        }
    }
    
    private void append(char character) {
        if (tokenBufferLength == tokenBuffer.length) {
            char[] newBuffer = new char[tokenBuffer.length * 2];
            System.arraycopy(tokenBuffer, 0, newBuffer, 0, tokenBuffer.length);
            tokenBuffer = newBuffer;
        }
        tokenBuffer[tokenBufferLength++] = character;
    }
    
    private void readComment() throws IOException {
        int nextChar;
        for (; ; ) {
            nextChar = readChar();
            switch (nextChar) {
            case -1: 
                throw new RuntimeException("Unclosed comment");
            
            case '*': 
                nextChar = readChar();
                if (nextChar == '/') {
                    return;
                } else if (nextChar == -1) {
                    throw new RuntimeException("Unclosed comment");
                } else {
                    pushChar(nextChar);
                }
                break;
            
            default: 
                break;
            
            }
        }
    }
    
    private void startBlock(int startToken) {
        if (stackCount == unitStack.length) {
            int[] newUS = new int[stackCount * 2];
            System.arraycopy(unitStack, 0, newUS, 0, stackCount);
            unitStack = newUS;
        }
        unitStack[stackCount++] = startToken;
    }
    
    private void endBlock(int endToken) {
        int startToken;
        switch (endToken) {
        case BRACKET_CLOSE: 
            startToken = BRACKET_OPEN;
            break;
        
        case BRACE_CLOSE: 
            startToken = BRACE_OPEN;
            break;
        
        case PAREN_CLOSE: 
            startToken = PAREN_OPEN;
            break;
        
        default: 
            startToken = -1;
            break;
        
        }
        if (stackCount > 0 && unitStack[stackCount - 1] == startToken) {
            stackCount--;
        } else {
            throw new RuntimeException("Unmatched block");
        }
    }
    
    private boolean inBlock() {
        return (stackCount > 0);
    }
    
    private int readWS() throws IOException {
        int nextChar;
        while ((nextChar = readChar()) != -1 && Character.isWhitespace((char)nextChar)) {
            readWS = true;
        }
        return nextChar;
    }
    
    private int readChar() throws IOException {
        if (didPushChar) {
            didPushChar = false;
            return pushedChar;
        }
        return reader.read();
    }
    
    private void pushChar(int tempChar) {
        if (didPushChar) {
            throw new RuntimeException("Can not handle look ahead of more than one character");
        }
        didPushChar = true;
        pushedChar = tempChar;
    }
}
