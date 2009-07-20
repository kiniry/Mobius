//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SourceTextMenu
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.source;

import java.util.Enumeration;

import jpov.viewer.JpovViewer;

import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.widgets.Menu;

/**
 * This class provides facilities to display the contextual menu of the source 
 * text when the right button is clicked on an highlighted box.
 * @author L. Burdy
 */
public class SourceTextMenu implements MouseListener {

    /**
     * The viewer where the menu should be displayed.
     **/
	private JpovViewer ew;
	
    /**
     * The menu to display
     **/
    private Menu stmenu;

    /**
     * Constructs a mouse listener to display the contextual menu
     * @param ew The viewer
     * @param m The menu
     **/
	public SourceTextMenu(JpovViewer ew, Menu m) {
		this.ew = ew;
		stmenu = m;
	}

    /**
     * Performs no action
     **/
	public void mouseDoubleClick(MouseEvent e) {
	}

    /**
     * Displays the menu on a mouse event if the right button is pressed down 
     * when a highlighted box is pointed.
     * @param e The mouse event.
     **/
	public void mouseDown(MouseEvent e) {
		if (ew != null && ew.getSelectedGoal() != null && e.button == 3) {
			Enumeration en = ew.getLeftTree().getEhl().getLabels();
			while (en.hasMoreElements()) {
				Box b = (Box) en.nextElement();
				if (b.includes(ew.getSourceView().getSourceText(), e.x, e.y)) {

					stmenu.getItem(0).setData("BOX", b);
					stmenu.getItem(0).setData("GOAL", ew.getSelectedGoal());
					stmenu.setVisible(true);
					break;
				}
			}
		}
	}

    /**
     * Performs no action
     **/
	public void mouseUp(MouseEvent e) {
	}

}