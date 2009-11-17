package java.awt;

class Cursor$CursorDisposer extends sun.java2d.DisposerRecord {
    
    Cursor$CursorDisposer() {
        
    }
    long pData;
    
    public void dispose() {
        Cursor.access$000(pData);
    }
}
