package java.awt.dnd.peer;

import java.awt.Cursor;
import java.awt.Image;
import java.awt.Point;
import java.awt.dnd.DragSourceContext;
import java.awt.dnd.InvalidDnDOperationException;

public interface DragSourceContextPeer {
    
    void startDrag(DragSourceContext dsc, Cursor c, Image dragImage, Point imageOffset) throws InvalidDnDOperationException;
    
    Cursor getCursor();
    
    void setCursor(Cursor c) throws InvalidDnDOperationException;
    
    void transferablesFlavorsChanged();
}
