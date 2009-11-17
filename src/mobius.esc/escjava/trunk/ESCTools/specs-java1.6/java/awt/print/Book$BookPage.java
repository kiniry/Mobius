package java.awt.print;

class Book$BookPage {
    /*synthetic*/ final Book this$0;
    private PageFormat mFormat;
    private Printable mPainter;
    
    Book$BookPage(/*synthetic*/ final Book this$0, Printable painter, PageFormat format) {
        this.this$0 = this$0;
        
        if (painter == null || format == null) {
            throw new NullPointerException();
        }
        mFormat = format;
        mPainter = painter;
    }
    
    Printable getPrintable() {
        return mPainter;
    }
    
    PageFormat getPageFormat() {
        return mFormat;
    }
}
