package java.awt.font;

import sun.font.TextLineComponent;

class TextLine$2 extends TextLine$Function {
    
    TextLine$2() {
        super(null);
    }
    
    float computeFunction(TextLine line, int componentIndex, int indexInArray) {
        TextLineComponent tlc = TextLine.access$100(line)[componentIndex];
        return tlc.getCharAdvance(indexInArray);
    }
}
