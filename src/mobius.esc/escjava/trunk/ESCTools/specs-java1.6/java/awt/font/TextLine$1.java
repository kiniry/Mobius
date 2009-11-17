package java.awt.font;

import sun.font.TextLineComponent;

class TextLine$1 extends TextLine$Function {
    
    TextLine$1() {
        super(null);
    }
    
    float computeFunction(TextLine line, int componentIndex, int indexInArray) {
        TextLineComponent tlc = TextLine.access$100(line)[componentIndex];
        int vi = TextLine.access$200(line) == null ? componentIndex : TextLine.access$200(line)[componentIndex];
        return TextLine.access$300(line)[vi * 2] + tlc.getCharX(indexInArray) + tlc.getCharAdvance(indexInArray);
    }
}
