package javax.swing;

final class LegacyLayoutFocusTraversalPolicy extends LayoutFocusTraversalPolicy {
    
    LegacyLayoutFocusTraversalPolicy(DefaultFocusManager defaultFocusManager) {
        super(new CompareTabOrderComparator(defaultFocusManager));
    }
}
