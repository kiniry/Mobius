package java.awt.datatransfer;

import java.io.*;
import java.nio.*;
import java.util.*;

class DataFlavor$TextFlavorComparator extends DataTransferer$DataFlavorComparator {
    
    DataFlavor$TextFlavorComparator() {
        
    }
    
    public int compare(Object obj1, Object obj2) {
        DataFlavor flavor1 = (DataFlavor)(DataFlavor)obj1;
        DataFlavor flavor2 = (DataFlavor)(DataFlavor)obj2;
        if (flavor1.isFlavorTextType()) {
            if (flavor2.isFlavorTextType()) {
                return super.compare(obj1, obj2);
            } else {
                return 1;
            }
        } else if (flavor2.isFlavorTextType()) {
            return -1;
        } else {
            return 0;
        }
    }
}
