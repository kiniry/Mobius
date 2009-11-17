package java.awt.font;

import sun.font.TextLineComponent;

class TextLine$4 extends TextLine$Function {
    
    TextLine$4() {
        super(null);
    }
    
    float computeFunction(TextLine line, int componentIndex, int indexInArray) {
        TextLineComponent tlc = TextLine.access$100(line)[componentIndex];
        float charPos = tlc.getCharY(indexInArray);
        return charPos + TextLine.access$400(line, componentIndex);
    }
}
