package java.util;

import java.io.IOException;
import java.io.InputStream;

class Properties$LineReader {
    /*synthetic*/ final Properties this$0;
    
    public Properties$LineReader(/*synthetic*/ final Properties this$0, InputStream inStream) {
        this.this$0 = this$0;
        
        this.inStream = inStream;
    }
    byte[] inBuf = new byte[8192];
    char[] lineBuf = new char[1024];
    int inLimit = 0;
    int inOff = 0;
    InputStream inStream;
    
    int readLine() throws IOException {
        int len = 0;
        char c = 0;
        boolean skipWhiteSpace = true;
        boolean isCommentLine = false;
        boolean isNewLine = true;
        boolean appendedLineBegin = false;
        boolean precedingBackslash = false;
        boolean skipLF = false;
        while (true) {
            if (inOff >= inLimit) {
                inLimit = inStream.read(inBuf);
                inOff = 0;
                if (inLimit <= 0) {
                    if (len == 0 || isCommentLine) {
                        return -1;
                    }
                    return len;
                }
            }
            c = (char)(255 & inBuf[inOff++]);
            if (skipLF) {
                skipLF = false;
                if (c == '\n') {
                    continue;
                }
            }
            if (skipWhiteSpace) {
                if (c == ' ' || c == '\t' || c == '\f') {
                    continue;
                }
                if (!appendedLineBegin && (c == '\r' || c == '\n')) {
                    continue;
                }
                skipWhiteSpace = false;
                appendedLineBegin = false;
            }
            if (isNewLine) {
                isNewLine = false;
                if (c == '#' || c == '!') {
                    isCommentLine = true;
                    continue;
                }
            }
            if (c != '\n' && c != '\r') {
                lineBuf[len++] = c;
                if (len == lineBuf.length) {
                    int newLength = lineBuf.length * 2;
                    if (newLength < 0) {
                        newLength = Integer.MAX_VALUE;
                    }
                    char[] buf = new char[newLength];
                    System.arraycopy(lineBuf, 0, buf, 0, lineBuf.length);
                    lineBuf = buf;
                }
                if (c == '\\') {
                    precedingBackslash = !precedingBackslash;
                } else {
                    precedingBackslash = false;
                }
            } else {
                if (isCommentLine || len == 0) {
                    isCommentLine = false;
                    isNewLine = true;
                    skipWhiteSpace = true;
                    len = 0;
                    continue;
                }
                if (inOff >= inLimit) {
                    inLimit = inStream.read(inBuf);
                    inOff = 0;
                    if (inLimit <= 0) {
                        return len;
                    }
                }
                if (precedingBackslash) {
                    len -= 1;
                    skipWhiteSpace = true;
                    appendedLineBegin = true;
                    precedingBackslash = false;
                    if (c == '\r') {
                        skipLF = true;
                    }
                } else {
                    return len;
                }
            }
        }
    }
}
