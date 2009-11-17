package java.awt.print;

public class PageFormat implements Cloneable {
    public static final int LANDSCAPE = 0;
    public static final int PORTRAIT = 1;
    public static final int REVERSE_LANDSCAPE = 2;
    private Paper mPaper;
    private int mOrientation = PORTRAIT;
    
    public PageFormat() {
        
        mPaper = new Paper();
    }
    
    public Object clone() {
        PageFormat newPage;
        try {
            newPage = (PageFormat)(PageFormat)super.clone();
            newPage.mPaper = (Paper)(Paper)mPaper.clone();
        } catch (CloneNotSupportedException e) {
            e.printStackTrace();
            newPage = null;
        }
        return newPage;
    }
    
    public double getWidth() {
        double width;
        int orientation = getOrientation();
        if (orientation == PORTRAIT) {
            width = mPaper.getWidth();
        } else {
            width = mPaper.getHeight();
        }
        return width;
    }
    
    public double getHeight() {
        double height;
        int orientation = getOrientation();
        if (orientation == PORTRAIT) {
            height = mPaper.getHeight();
        } else {
            height = mPaper.getWidth();
        }
        return height;
    }
    
    public double getImageableX() {
        double x;
        switch (getOrientation()) {
        case LANDSCAPE: 
            x = mPaper.getHeight() - (mPaper.getImageableY() + mPaper.getImageableHeight());
            break;
        
        case PORTRAIT: 
            x = mPaper.getImageableX();
            break;
        
        case REVERSE_LANDSCAPE: 
            x = mPaper.getImageableY();
            break;
        
        default: 
            throw new InternalError("unrecognized orientation");
        
        }
        return x;
    }
    
    public double getImageableY() {
        double y;
        switch (getOrientation()) {
        case LANDSCAPE: 
            y = mPaper.getImageableX();
            break;
        
        case PORTRAIT: 
            y = mPaper.getImageableY();
            break;
        
        case REVERSE_LANDSCAPE: 
            y = mPaper.getWidth() - (mPaper.getImageableX() + mPaper.getImageableWidth());
            break;
        
        default: 
            throw new InternalError("unrecognized orientation");
        
        }
        return y;
    }
    
    public double getImageableWidth() {
        double width;
        if (getOrientation() == PORTRAIT) {
            width = mPaper.getImageableWidth();
        } else {
            width = mPaper.getImageableHeight();
        }
        return width;
    }
    
    public double getImageableHeight() {
        double height;
        if (getOrientation() == PORTRAIT) {
            height = mPaper.getImageableHeight();
        } else {
            height = mPaper.getImageableWidth();
        }
        return height;
    }
    
    public Paper getPaper() {
        return (Paper)(Paper)mPaper.clone();
    }
    
    public void setPaper(Paper paper) {
        mPaper = (Paper)(Paper)paper.clone();
    }
    
    public void setOrientation(int orientation) throws IllegalArgumentException {
        if (0 <= orientation && orientation <= REVERSE_LANDSCAPE) {
            mOrientation = orientation;
        } else {
            throw new IllegalArgumentException();
        }
    }
    
    public int getOrientation() {
        return mOrientation;
    }
    
    public double[] getMatrix() {
        double[] matrix = new double[6];
        switch (mOrientation) {
        case LANDSCAPE: 
            matrix[0] = 0;
            matrix[1] = -1;
            matrix[2] = 1;
            matrix[3] = 0;
            matrix[4] = 0;
            matrix[5] = mPaper.getHeight();
            break;
        
        case PORTRAIT: 
            matrix[0] = 1;
            matrix[1] = 0;
            matrix[2] = 0;
            matrix[3] = 1;
            matrix[4] = 0;
            matrix[5] = 0;
            break;
        
        case REVERSE_LANDSCAPE: 
            matrix[0] = 0;
            matrix[1] = 1;
            matrix[2] = -1;
            matrix[3] = 0;
            matrix[4] = mPaper.getWidth();
            matrix[5] = 0;
            break;
        
        default: 
            throw new IllegalArgumentException();
        
        }
        return matrix;
    }
}
