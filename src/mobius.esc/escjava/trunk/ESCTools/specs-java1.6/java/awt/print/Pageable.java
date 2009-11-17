package java.awt.print;

public interface Pageable {
    int UNKNOWN_NUMBER_OF_PAGES = -1;
    
    int getNumberOfPages();
    
    PageFormat getPageFormat(int pageIndex) throws IndexOutOfBoundsException;
    
    Printable getPrintable(int pageIndex) throws IndexOutOfBoundsException;
}
