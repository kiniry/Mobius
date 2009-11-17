package java.awt.print;

import java.util.Vector;

public class Book implements Pageable {
    private Vector mPages;
    
    public Book() {
        
        mPages = new Vector();
    }
    
    public int getNumberOfPages() {
        return mPages.size();
    }
    
    public PageFormat getPageFormat(int pageIndex) throws IndexOutOfBoundsException {
        return getPage(pageIndex).getPageFormat();
    }
    
    public Printable getPrintable(int pageIndex) throws IndexOutOfBoundsException {
        return getPage(pageIndex).getPrintable();
    }
    
    public void setPage(int pageIndex, Printable painter, PageFormat page) throws IndexOutOfBoundsException {
        if (painter == null) {
            throw new NullPointerException("painter is null");
        }
        if (page == null) {
            throw new NullPointerException("page is null");
        }
        mPages.setElementAt(new Book$BookPage(this, painter, page), pageIndex);
    }
    
    public void append(Printable painter, PageFormat page) {
        mPages.addElement(new Book$BookPage(this, painter, page));
    }
    
    public void append(Printable painter, PageFormat page, int numPages) {
        Book$BookPage bookPage = new Book$BookPage(this, painter, page);
        int pageIndex = mPages.size();
        int newSize = pageIndex + numPages;
        mPages.setSize(newSize);
        for (int i = pageIndex; i < newSize; i++) {
            mPages.setElementAt(bookPage, i);
        }
    }
    
    private Book$BookPage getPage(int pageIndex) throws ArrayIndexOutOfBoundsException {
        return (Book$BookPage)(Book$BookPage)mPages.elementAt(pageIndex);
    }
    {
    }
}
