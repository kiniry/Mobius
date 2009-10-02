package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.io.*;
import javax.swing.tree.*;
import sun.swing.UIAction;

class BasicTreeUI$Actions extends UIAction {
    
    /*synthetic*/ static void access$1100(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2) {
        x0.cancelEditing(x1, x2);
    }
    
    /*synthetic*/ static void access$1000(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2) {
        x0.toggle(x1, x2);
    }
    
    /*synthetic*/ static void access$900(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2, int x3, boolean x4, boolean x5) {
        x0.home(x1, x2, x3, x4, x5);
    }
    
    /*synthetic*/ static void access$800(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2, int x3, boolean x4, boolean x5) {
        x0.increment(x1, x2, x3, x4, x5);
    }
    
    /*synthetic*/ static void access$700(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2, int x3, boolean x4, boolean x5) {
        x0.page(x1, x2, x3, x4, x5);
    }
    
    /*synthetic*/ static void access$600(BasicTreeUI$Actions x0, JTree x1, BasicTreeUI x2, int x3, boolean x4) {
        x0.traverse(x1, x2, x3, x4);
    }
    private static final String SELECT_PREVIOUS = "selectPrevious";
    private static final String SELECT_PREVIOUS_CHANGE_LEAD = "selectPreviousChangeLead";
    private static final String SELECT_PREVIOUS_EXTEND_SELECTION = "selectPreviousExtendSelection";
    private static final String SELECT_NEXT = "selectNext";
    private static final String SELECT_NEXT_CHANGE_LEAD = "selectNextChangeLead";
    private static final String SELECT_NEXT_EXTEND_SELECTION = "selectNextExtendSelection";
    private static final String SELECT_CHILD = "selectChild";
    private static final String SELECT_CHILD_CHANGE_LEAD = "selectChildChangeLead";
    private static final String SELECT_PARENT = "selectParent";
    private static final String SELECT_PARENT_CHANGE_LEAD = "selectParentChangeLead";
    private static final String SCROLL_UP_CHANGE_SELECTION = "scrollUpChangeSelection";
    private static final String SCROLL_UP_CHANGE_LEAD = "scrollUpChangeLead";
    private static final String SCROLL_UP_EXTEND_SELECTION = "scrollUpExtendSelection";
    private static final String SCROLL_DOWN_CHANGE_SELECTION = "scrollDownChangeSelection";
    private static final String SCROLL_DOWN_EXTEND_SELECTION = "scrollDownExtendSelection";
    private static final String SCROLL_DOWN_CHANGE_LEAD = "scrollDownChangeLead";
    private static final String SELECT_FIRST = "selectFirst";
    private static final String SELECT_FIRST_CHANGE_LEAD = "selectFirstChangeLead";
    private static final String SELECT_FIRST_EXTEND_SELECTION = "selectFirstExtendSelection";
    private static final String SELECT_LAST = "selectLast";
    private static final String SELECT_LAST_CHANGE_LEAD = "selectLastChangeLead";
    private static final String SELECT_LAST_EXTEND_SELECTION = "selectLastExtendSelection";
    private static final String TOGGLE = "toggle";
    private static final String CANCEL_EDITING = "cancel";
    private static final String START_EDITING = "startEditing";
    private static final String SELECT_ALL = "selectAll";
    private static final String CLEAR_SELECTION = "clearSelection";
    private static final String SCROLL_LEFT = "scrollLeft";
    private static final String SCROLL_RIGHT = "scrollRight";
    private static final String SCROLL_LEFT_EXTEND_SELECTION = "scrollLeftExtendSelection";
    private static final String SCROLL_RIGHT_EXTEND_SELECTION = "scrollRightExtendSelection";
    private static final String SCROLL_RIGHT_CHANGE_LEAD = "scrollRightChangeLead";
    private static final String SCROLL_LEFT_CHANGE_LEAD = "scrollLeftChangeLead";
    private static final String EXPAND = "expand";
    private static final String COLLAPSE = "collapse";
    private static final String MOVE_SELECTION_TO_PARENT = "moveSelectionToParent";
    private static final String ADD_TO_SELECTION = "addToSelection";
    private static final String TOGGLE_AND_ANCHOR = "toggleAndAnchor";
    private static final String EXTEND_TO = "extendTo";
    private static final String MOVE_SELECTION_TO = "moveSelectionTo";
    
    BasicTreeUI$Actions() {
        super(null);
    }
    
    BasicTreeUI$Actions(String key) {
        super(key);
    }
    
    public boolean isEnabled(Object o) {
        if (o instanceof JTree) {
            if (getName() == CANCEL_EDITING) {
                return ((JTree)(JTree)o).isEditing();
            }
        }
        return true;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTree tree = (JTree)(JTree)e.getSource();
        BasicTreeUI ui = (BasicTreeUI)(BasicTreeUI)BasicLookAndFeel.getUIOfType(tree.getUI(), BasicTreeUI.class);
        if (ui == null) {
            return;
        }
        String key = getName();
        if (key == SELECT_PREVIOUS) {
            increment(tree, ui, -1, false, true);
        } else if (key == SELECT_PREVIOUS_CHANGE_LEAD) {
            increment(tree, ui, -1, false, false);
        } else if (key == SELECT_PREVIOUS_EXTEND_SELECTION) {
            increment(tree, ui, -1, true, true);
        } else if (key == SELECT_NEXT) {
            increment(tree, ui, 1, false, true);
        } else if (key == SELECT_NEXT_CHANGE_LEAD) {
            increment(tree, ui, 1, false, false);
        } else if (key == SELECT_NEXT_EXTEND_SELECTION) {
            increment(tree, ui, 1, true, true);
        } else if (key == SELECT_CHILD) {
            traverse(tree, ui, 1, true);
        } else if (key == SELECT_CHILD_CHANGE_LEAD) {
            traverse(tree, ui, 1, false);
        } else if (key == SELECT_PARENT) {
            traverse(tree, ui, -1, true);
        } else if (key == SELECT_PARENT_CHANGE_LEAD) {
            traverse(tree, ui, -1, false);
        } else if (key == SCROLL_UP_CHANGE_SELECTION) {
            page(tree, ui, -1, false, true);
        } else if (key == SCROLL_UP_CHANGE_LEAD) {
            page(tree, ui, -1, false, false);
        } else if (key == SCROLL_UP_EXTEND_SELECTION) {
            page(tree, ui, -1, true, true);
        } else if (key == SCROLL_DOWN_CHANGE_SELECTION) {
            page(tree, ui, 1, false, true);
        } else if (key == SCROLL_DOWN_EXTEND_SELECTION) {
            page(tree, ui, 1, true, true);
        } else if (key == SCROLL_DOWN_CHANGE_LEAD) {
            page(tree, ui, 1, false, false);
        } else if (key == SELECT_FIRST) {
            home(tree, ui, -1, false, true);
        } else if (key == SELECT_FIRST_CHANGE_LEAD) {
            home(tree, ui, -1, false, false);
        } else if (key == SELECT_FIRST_EXTEND_SELECTION) {
            home(tree, ui, -1, true, true);
        } else if (key == SELECT_LAST) {
            home(tree, ui, 1, false, true);
        } else if (key == SELECT_LAST_CHANGE_LEAD) {
            home(tree, ui, 1, false, false);
        } else if (key == SELECT_LAST_EXTEND_SELECTION) {
            home(tree, ui, 1, true, true);
        } else if (key == TOGGLE) {
            toggle(tree, ui);
        } else if (key == CANCEL_EDITING) {
            cancelEditing(tree, ui);
        } else if (key == START_EDITING) {
            startEditing(tree, ui);
        } else if (key == SELECT_ALL) {
            selectAll(tree, ui, true);
        } else if (key == CLEAR_SELECTION) {
            selectAll(tree, ui, false);
        } else if (key == ADD_TO_SELECTION) {
            if (ui.getRowCount(tree) > 0) {
                int lead = BasicTreeUI.access$2300(ui);
                if (!tree.isRowSelected(lead)) {
                    TreePath aPath = BasicTreeUI.access$2400(ui);
                    tree.addSelectionRow(lead);
                    BasicTreeUI.access$1900(ui, aPath);
                }
            }
        } else if (key == TOGGLE_AND_ANCHOR) {
            if (ui.getRowCount(tree) > 0) {
                int lead = BasicTreeUI.access$2300(ui);
                TreePath lPath = BasicTreeUI.access$1800(ui);
                if (!tree.isRowSelected(lead)) {
                    tree.addSelectionRow(lead);
                } else {
                    tree.removeSelectionRow(lead);
                    BasicTreeUI.access$2000(ui, lPath);
                }
                BasicTreeUI.access$1900(ui, lPath);
            }
        } else if (key == EXTEND_TO) {
            extendSelection(tree, ui);
        } else if (key == MOVE_SELECTION_TO) {
            if (ui.getRowCount(tree) > 0) {
                int lead = BasicTreeUI.access$2300(ui);
                tree.setSelectionInterval(lead, lead);
            }
        } else if (key == SCROLL_LEFT) {
            scroll(tree, ui, SwingConstants.HORIZONTAL, -10);
        } else if (key == SCROLL_RIGHT) {
            scroll(tree, ui, SwingConstants.HORIZONTAL, 10);
        } else if (key == SCROLL_LEFT_EXTEND_SELECTION) {
            scrollChangeSelection(tree, ui, -1, true, true);
        } else if (key == SCROLL_RIGHT_EXTEND_SELECTION) {
            scrollChangeSelection(tree, ui, 1, true, true);
        } else if (key == SCROLL_RIGHT_CHANGE_LEAD) {
            scrollChangeSelection(tree, ui, 1, false, false);
        } else if (key == SCROLL_LEFT_CHANGE_LEAD) {
            scrollChangeSelection(tree, ui, -1, false, false);
        } else if (key == EXPAND) {
            expand(tree, ui);
        } else if (key == COLLAPSE) {
            collapse(tree, ui);
        } else if (key == MOVE_SELECTION_TO_PARENT) {
            moveSelectionToParent(tree, ui);
        }
    }
    
    private void scrollChangeSelection(JTree tree, BasicTreeUI ui, int direction, boolean addToSelection, boolean changeSelection) {
        int rowCount;
        if ((rowCount = ui.getRowCount(tree)) > 0 && ui.treeSelectionModel != null) {
            TreePath newPath;
            Rectangle visRect = tree.getVisibleRect();
            if (direction == -1) {
                newPath = ui.getClosestPathForLocation(tree, visRect.x, visRect.y);
                visRect.x = Math.max(0, visRect.x - visRect.width);
            } else {
                visRect.x = Math.min(Math.max(0, tree.getWidth() - visRect.width), visRect.x + visRect.width);
                newPath = ui.getClosestPathForLocation(tree, visRect.x, visRect.y + visRect.height);
            }
            tree.scrollRectToVisible(visRect);
            if (addToSelection) {
                BasicTreeUI.access$2500(ui, newPath);
            } else if (changeSelection) {
                tree.setSelectionPath(newPath);
            } else {
                BasicTreeUI.access$2100(ui, newPath, true);
            }
        }
    }
    
    private void scroll(JTree component, BasicTreeUI ui, int direction, int amount) {
        Rectangle visRect = component.getVisibleRect();
        Dimension size = component.getSize();
        if (direction == SwingConstants.HORIZONTAL) {
            visRect.x += amount;
            visRect.x = Math.max(0, visRect.x);
            visRect.x = Math.min(Math.max(0, size.width - visRect.width), visRect.x);
        } else {
            visRect.y += amount;
            visRect.y = Math.max(0, visRect.y);
            visRect.y = Math.min(Math.max(0, size.width - visRect.height), visRect.y);
        }
        component.scrollRectToVisible(visRect);
    }
    
    private void extendSelection(JTree tree, BasicTreeUI ui) {
        if (ui.getRowCount(tree) > 0) {
            int lead = BasicTreeUI.access$2300(ui);
            if (lead != -1) {
                TreePath leadP = BasicTreeUI.access$1800(ui);
                TreePath aPath = BasicTreeUI.access$2400(ui);
                int aRow = ui.getRowForPath(tree, aPath);
                if (aRow == -1) aRow = 0;
                tree.setSelectionInterval(aRow, lead);
                BasicTreeUI.access$2000(ui, leadP);
                BasicTreeUI.access$1900(ui, aPath);
            }
        }
    }
    
    private void selectAll(JTree tree, BasicTreeUI ui, boolean selectAll) {
        int rowCount = ui.getRowCount(tree);
        if (rowCount > 0) {
            if (selectAll) {
                if (tree.getSelectionModel().getSelectionMode() == TreeSelectionModel.SINGLE_TREE_SELECTION) {
                    int lead = BasicTreeUI.access$2300(ui);
                    if (lead != -1) {
                        tree.setSelectionRow(lead);
                    } else if (tree.getMinSelectionRow() == -1) {
                        tree.setSelectionRow(0);
                        ui.ensureRowsAreVisible(0, 0);
                    }
                    return;
                }
                TreePath lastPath = BasicTreeUI.access$1800(ui);
                TreePath aPath = BasicTreeUI.access$2400(ui);
                if (lastPath != null && !tree.isVisible(lastPath)) {
                    lastPath = null;
                }
                tree.setSelectionInterval(0, rowCount - 1);
                if (lastPath != null) {
                    BasicTreeUI.access$2000(ui, lastPath);
                }
                if (aPath != null && tree.isVisible(aPath)) {
                    BasicTreeUI.access$1900(ui, aPath);
                }
            } else {
                TreePath lastPath = BasicTreeUI.access$1800(ui);
                TreePath aPath = BasicTreeUI.access$2400(ui);
                tree.clearSelection();
                BasicTreeUI.access$1900(ui, aPath);
                BasicTreeUI.access$2000(ui, lastPath);
            }
        }
    }
    
    private void startEditing(JTree tree, BasicTreeUI ui) {
        TreePath lead = BasicTreeUI.access$1800(ui);
        int editRow = (lead != null) ? ui.getRowForPath(tree, lead) : -1;
        if (editRow != -1) {
            tree.startEditingAtPath(lead);
        }
    }
    
    private void cancelEditing(JTree tree, BasicTreeUI ui) {
        tree.cancelEditing();
    }
    
    private void toggle(JTree tree, BasicTreeUI ui) {
        int selRow = BasicTreeUI.access$2300(ui);
        if (selRow != -1 && !ui.isLeaf(selRow)) {
            TreePath aPath = BasicTreeUI.access$2400(ui);
            TreePath lPath = BasicTreeUI.access$1800(ui);
            ui.toggleExpandState(ui.getPathForRow(tree, selRow));
            BasicTreeUI.access$1900(ui, aPath);
            BasicTreeUI.access$2000(ui, lPath);
        }
    }
    
    private void expand(JTree tree, BasicTreeUI ui) {
        int selRow = BasicTreeUI.access$2300(ui);
        tree.expandRow(selRow);
    }
    
    private void collapse(JTree tree, BasicTreeUI ui) {
        int selRow = BasicTreeUI.access$2300(ui);
        tree.collapseRow(selRow);
    }
    
    private void increment(JTree tree, BasicTreeUI ui, int direction, boolean addToSelection, boolean changeSelection) {
        if (!addToSelection && !changeSelection && tree.getSelectionModel().getSelectionMode() != TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) {
            changeSelection = true;
        }
        int rowCount;
        if (ui.treeSelectionModel != null && (rowCount = tree.getRowCount()) > 0) {
            int selIndex = BasicTreeUI.access$2300(ui);
            int newIndex;
            if (selIndex == -1) {
                if (direction == 1) newIndex = 0; else newIndex = rowCount - 1;
            } else newIndex = Math.min(rowCount - 1, Math.max(0, (selIndex + direction)));
            if (addToSelection && ui.treeSelectionModel.getSelectionMode() != TreeSelectionModel.SINGLE_TREE_SELECTION) {
                BasicTreeUI.access$2500(ui, tree.getPathForRow(newIndex));
            } else if (changeSelection) {
                tree.setSelectionInterval(newIndex, newIndex);
            } else {
                BasicTreeUI.access$2100(ui, tree.getPathForRow(newIndex), true);
            }
            ui.ensureRowsAreVisible(newIndex, newIndex);
            ui.lastSelectedRow = newIndex;
        }
    }
    
    private void traverse(JTree tree, BasicTreeUI ui, int direction, boolean changeSelection) {
        if (!changeSelection && tree.getSelectionModel().getSelectionMode() != TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) {
            changeSelection = true;
        }
        int rowCount;
        if ((rowCount = tree.getRowCount()) > 0) {
            int minSelIndex = BasicTreeUI.access$2300(ui);
            int newIndex;
            if (minSelIndex == -1) newIndex = 0; else {
                if (direction == 1) {
                    if (!ui.isLeaf(minSelIndex) && !tree.isExpanded(minSelIndex)) {
                        ui.toggleExpandState(ui.getPathForRow(tree, minSelIndex));
                        newIndex = -1;
                    } else newIndex = Math.min(minSelIndex + 1, rowCount - 1);
                } else {
                    if (!ui.isLeaf(minSelIndex) && tree.isExpanded(minSelIndex)) {
                        ui.toggleExpandState(ui.getPathForRow(tree, minSelIndex));
                        newIndex = -1;
                    } else {
                        TreePath path = ui.getPathForRow(tree, minSelIndex);
                        if (path != null && path.getPathCount() > 1) {
                            newIndex = ui.getRowForPath(tree, path.getParentPath());
                        } else newIndex = -1;
                    }
                }
            }
            if (newIndex != -1) {
                if (changeSelection) {
                    tree.setSelectionInterval(newIndex, newIndex);
                } else {
                    BasicTreeUI.access$2100(ui, ui.getPathForRow(tree, newIndex), true);
                }
                ui.ensureRowsAreVisible(newIndex, newIndex);
            }
        }
    }
    
    private void moveSelectionToParent(JTree tree, BasicTreeUI ui) {
        int selRow = BasicTreeUI.access$2300(ui);
        TreePath path = ui.getPathForRow(tree, selRow);
        if (path != null && path.getPathCount() > 1) {
            int newIndex = ui.getRowForPath(tree, path.getParentPath());
            if (newIndex != -1) {
                tree.setSelectionInterval(newIndex, newIndex);
                ui.ensureRowsAreVisible(newIndex, newIndex);
            }
        }
    }
    
    private void page(JTree tree, BasicTreeUI ui, int direction, boolean addToSelection, boolean changeSelection) {
        if (!addToSelection && !changeSelection && tree.getSelectionModel().getSelectionMode() != TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) {
            changeSelection = true;
        }
        int rowCount;
        if ((rowCount = ui.getRowCount(tree)) > 0 && ui.treeSelectionModel != null) {
            Dimension maxSize = tree.getSize();
            TreePath lead = BasicTreeUI.access$1800(ui);
            TreePath newPath;
            Rectangle visRect = tree.getVisibleRect();
            if (direction == -1) {
                newPath = ui.getClosestPathForLocation(tree, visRect.x, visRect.y);
                if (newPath.equals(lead)) {
                    visRect.y = Math.max(0, visRect.y - visRect.height);
                    newPath = tree.getClosestPathForLocation(visRect.x, visRect.y);
                }
            } else {
                visRect.y = Math.min(maxSize.height, visRect.y + visRect.height - 1);
                newPath = tree.getClosestPathForLocation(visRect.x, visRect.y);
                if (newPath.equals(lead)) {
                    visRect.y = Math.min(maxSize.height, visRect.y + visRect.height - 1);
                    newPath = tree.getClosestPathForLocation(visRect.x, visRect.y);
                }
            }
            Rectangle newRect = ui.getPathBounds(tree, newPath);
            newRect.x = visRect.x;
            newRect.width = visRect.width;
            if (direction == -1) {
                newRect.height = visRect.height;
            } else {
                newRect.y -= (visRect.height - newRect.height);
                newRect.height = visRect.height;
            }
            if (addToSelection) {
                BasicTreeUI.access$2500(ui, newPath);
            } else if (changeSelection) {
                tree.setSelectionPath(newPath);
            } else {
                BasicTreeUI.access$2100(ui, newPath, true);
            }
            tree.scrollRectToVisible(newRect);
        }
    }
    
    private void home(JTree tree, BasicTreeUI ui, int direction, boolean addToSelection, boolean changeSelection) {
        if (!addToSelection && !changeSelection && tree.getSelectionModel().getSelectionMode() != TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION) {
            changeSelection = true;
        }
        int rowCount = ui.getRowCount(tree);
        if (rowCount > 0) {
            if (direction == -1) {
                ui.ensureRowsAreVisible(0, 0);
                if (addToSelection) {
                    TreePath aPath = BasicTreeUI.access$2400(ui);
                    int aRow = (aPath == null) ? -1 : ui.getRowForPath(tree, aPath);
                    if (aRow == -1) {
                        tree.setSelectionInterval(0, 0);
                    } else {
                        tree.setSelectionInterval(0, aRow);
                        BasicTreeUI.access$1900(ui, aPath);
                        BasicTreeUI.access$2000(ui, ui.getPathForRow(tree, 0));
                    }
                } else if (changeSelection) {
                    tree.setSelectionInterval(0, 0);
                } else {
                    BasicTreeUI.access$2100(ui, ui.getPathForRow(tree, 0), true);
                }
            } else {
                ui.ensureRowsAreVisible(rowCount - 1, rowCount - 1);
                if (addToSelection) {
                    TreePath aPath = BasicTreeUI.access$2400(ui);
                    int aRow = (aPath == null) ? -1 : ui.getRowForPath(tree, aPath);
                    if (aRow == -1) {
                        tree.setSelectionInterval(rowCount - 1, rowCount - 1);
                    } else {
                        tree.setSelectionInterval(aRow, rowCount - 1);
                        BasicTreeUI.access$1900(ui, aPath);
                        BasicTreeUI.access$2000(ui, ui.getPathForRow(tree, rowCount - 1));
                    }
                } else if (changeSelection) {
                    tree.setSelectionInterval(rowCount - 1, rowCount - 1);
                } else {
                    BasicTreeUI.access$2100(ui, ui.getPathForRow(tree, rowCount - 1), true);
                }
            }
        }
    }
}
