package java.awt.font;

import java.lang.String;

public final class TextHitInfo {
    private int charIndex;
    private boolean isLeadingEdge;
    
    private TextHitInfo(int charIndex, boolean isLeadingEdge) {
        
        this.charIndex = charIndex;
        this.isLeadingEdge = isLeadingEdge;
    }
    
    public int getCharIndex() {
        return charIndex;
    }
    
    public boolean isLeadingEdge() {
        return isLeadingEdge;
    }
    
    public int getInsertionIndex() {
        return isLeadingEdge ? charIndex : charIndex + 1;
    }
    
    public int hashCode() {
        return charIndex;
    }
    
    public boolean equals(Object obj) {
        return (obj instanceof TextHitInfo) && equals((TextHitInfo)(TextHitInfo)obj);
    }
    
    public boolean equals(TextHitInfo hitInfo) {
        return hitInfo != null && charIndex == hitInfo.charIndex && isLeadingEdge == hitInfo.isLeadingEdge;
    }
    
    public String toString() {
        return "TextHitInfo[" + charIndex + (isLeadingEdge ? "L" : "T") + "]";
    }
    
    public static TextHitInfo leading(int charIndex) {
        return new TextHitInfo(charIndex, true);
    }
    
    public static TextHitInfo trailing(int charIndex) {
        return new TextHitInfo(charIndex, false);
    }
    
    public static TextHitInfo beforeOffset(int offset) {
        return new TextHitInfo(offset - 1, false);
    }
    
    public static TextHitInfo afterOffset(int offset) {
        return new TextHitInfo(offset, true);
    }
    
    public TextHitInfo getOtherHit() {
        if (isLeadingEdge) {
            return trailing(charIndex - 1);
        } else {
            return leading(charIndex + 1);
        }
    }
    
    public TextHitInfo getOffsetHit(int delta) {
        return new TextHitInfo(charIndex + delta, isLeadingEdge);
    }
}
