package javax.swing;

import java.awt.LayoutManager;
import java.awt.Component;
import java.awt.Container;
import java.awt.Point;
import java.awt.Dimension;
import java.awt.Insets;
import java.io.Serializable;

public class ViewportLayout implements LayoutManager, Serializable {
    
    public ViewportLayout() {
        
    }
    static ViewportLayout SHARED_INSTANCE = new ViewportLayout();
    
    public void addLayoutComponent(String name, Component c) {
    }
    
    public void removeLayoutComponent(Component c) {
    }
    
    public Dimension preferredLayoutSize(Container parent) {
        Component view = ((JViewport)(JViewport)parent).getView();
        if (view == null) {
            return new Dimension(0, 0);
        } else if (view instanceof Scrollable) {
            return ((Scrollable)(Scrollable)view).getPreferredScrollableViewportSize();
        } else {
            return view.getPreferredSize();
        }
    }
    
    public Dimension minimumLayoutSize(Container parent) {
        return new Dimension(4, 4);
    }
    
    public void layoutContainer(Container parent) {
        JViewport vp = (JViewport)(JViewport)parent;
        Component view = vp.getView();
        Scrollable scrollableView = null;
        if (view == null) {
            return;
        } else if (view instanceof Scrollable) {
            scrollableView = (Scrollable)(Scrollable)view;
        }
        Insets insets = vp.getInsets();
        Dimension viewPrefSize = view.getPreferredSize();
        Dimension vpSize = vp.getSize();
        Dimension extentSize = vp.toViewCoordinates(vpSize);
        Dimension viewSize = new Dimension(viewPrefSize);
        if (scrollableView != null) {
            if (scrollableView.getScrollableTracksViewportWidth()) {
                viewSize.width = vpSize.width;
            }
            if (scrollableView.getScrollableTracksViewportHeight()) {
                viewSize.height = vpSize.height;
            }
        }
        Point viewPosition = vp.getViewPosition();
        if (scrollableView == null || vp.getParent() == null || vp.getParent().getComponentOrientation().isLeftToRight()) {
            if ((viewPosition.x + extentSize.width) > viewSize.width) {
                viewPosition.x = Math.max(0, viewSize.width - extentSize.width);
            }
        } else {
            if (extentSize.width > viewSize.width) {
                viewPosition.x = viewSize.width - extentSize.width;
            } else {
                viewPosition.x = Math.max(0, Math.min(viewSize.width - extentSize.width, viewPosition.x));
            }
        }
        if ((viewPosition.y + extentSize.height) > viewSize.height) {
            viewPosition.y = Math.max(0, viewSize.height - extentSize.height);
        }
        if (scrollableView == null) {
            if ((viewPosition.x == 0) && (vpSize.width > viewPrefSize.width)) {
                viewSize.width = vpSize.width;
            }
            if ((viewPosition.y == 0) && (vpSize.height > viewPrefSize.height)) {
                viewSize.height = vpSize.height;
            }
        }
        vp.setViewPosition(viewPosition);
        vp.setViewSize(viewSize);
    }
}
