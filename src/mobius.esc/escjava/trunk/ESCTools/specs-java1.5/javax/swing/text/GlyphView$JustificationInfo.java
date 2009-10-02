package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;
import java.util.BitSet;

class GlyphView$JustificationInfo {
    final int start;
    final int end;
    final int leadingSpaces;
    final int contentSpaces;
    final int trailingSpaces;
    final boolean hasTab;
    final BitSet spaceMap;
    
    GlyphView$JustificationInfo(int start, int end, int leadingSpaces, int contentSpaces, int trailingSpaces, boolean hasTab, BitSet spaceMap) {
        
        this.start = start;
        this.end = end;
        this.leadingSpaces = leadingSpaces;
        this.contentSpaces = contentSpaces;
        this.trailingSpaces = trailingSpaces;
        this.hasTab = hasTab;
        this.spaceMap = spaceMap;
    }
}
