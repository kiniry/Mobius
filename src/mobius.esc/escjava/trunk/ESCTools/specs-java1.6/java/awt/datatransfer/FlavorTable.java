package java.awt.datatransfer;

import java.util.List;

public interface FlavorTable extends FlavorMap {
    
    List getNativesForFlavor(DataFlavor flav);
    
    List getFlavorsForNative(String nat);
}
