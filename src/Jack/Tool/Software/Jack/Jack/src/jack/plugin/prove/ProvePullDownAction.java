package jack.plugin.prove;

import jack.plugin.ToolbarButton;

import java.net.URL;
import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.IWorkbenchWindowPulldownDelegate;
import org.osgi.framework.Bundle;

//see: package org.eclipse.jdt.internal.ui.wizards.NewTypeDropDownAction

public class ProvePullDownAction extends Action implements IWorkbenchWindowPulldownDelegate{

	private Menu fMenu;
	ProverAction[] actions;
	Control fParent;
	public Menu getMenu(Control parent) {
		fParent = parent;
		if (fMenu == null) {
			fMenu= new Menu(parent);
			
			
			for (int i= 0; i < actions.length; i++) {
				ActionContributionItem item= new ActionContributionItem(actions[i]);
				item.fill(fMenu, -1);				
			}			
		
		}
		return fMenu;
	}

	private ProverAction[] getActionFromDescriptors() {
		ArrayList containers= new ArrayList();	
		IExtensionPoint extensionPoint = Platform.getExtensionRegistry().getExtensionPoint("org.eclipse.ui.actionSets");
		if (extensionPoint != null) {
			IConfigurationElement[] elements = extensionPoint.getConfigurationElements();
			for (int i = 0; i < elements.length; i++) {
				IConfigurationElement element= elements[i];
				if(element.getAttribute("id").startsWith("jack.provers.")) {
					IConfigurationElement [] elems =element.getChildren();
					for(int j = 0; j<elems.length; j++) {
						if(elems[j].getName().equals("action")) {
							try {
								ToolbarButton tb = (ToolbarButton)elems[j].createExecutableExtension("class");
								ProverAction a = new ProverAction(this, elems[j], tb);
								containers.add(a);
							} catch (CoreException e) {}
						}
					}
				}
			}
		}
		return (ProverAction[]) containers.toArray(new ProverAction[containers.size()]);
	}

	public void dispose() {
		if (fMenu != null) {
			fMenu.dispose();
			fMenu= null;
		}
	}

	public void run(IAction action) {
		if(fParent != null) {
		
		}
		
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#init(org.eclipse.ui.IWorkbenchWindow)
	 */
	public void init(IWorkbenchWindow window) {	
		actions= getActionFromDescriptors();
		setDefault();
	}



	private void setDefault() {
		if(actions.length >0) {
			actions[0].getDescription();
			this.setImageDescriptor(actions[0].getImageDescriptor());
		}
	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		for(int i = 0; i < actions.length; i++) {
			actions[i].selectionChanged(action, selection);
		}
	}
	public class ProverAction extends Action {

		private final static String ATT_NAME = "label";//$NON-NLS-1$
		private final static String ATT_ICON = "icon";//$NON-NLS-1$
		private static final String TAG_DESCRIPTION = "tooltip";	//$NON-NLS-1$
		
		private IConfigurationElement fConfigurationElement;
		IWorkbenchWindowActionDelegate  fTb;
		ProvePullDownAction fAction;
		public ProverAction(ProvePullDownAction action, IConfigurationElement element, ToolbarButton tb) {
			fConfigurationElement= element;
			fTb = tb;
			fAction = action;
			
			setText(element.getAttribute(ATT_NAME));
			String description= element.getAttribute(TAG_DESCRIPTION);
			setDescription(description);
			setToolTipText(description);
			setImageDescriptor(getIconFromConfig(fConfigurationElement));
		}

		private ImageDescriptor getIconFromConfig(IConfigurationElement config) {
			String iconName = config.getAttribute(ATT_ICON);
			if (iconName != null) {
				Bundle bundle= Platform.getBundle(config.getNamespace());
				URL url = bundle.getEntry(iconName);
				return ImageDescriptor.createFromURL(url);
			}
			return null;
		}

	
		public void run() {
			fTb.run(this);
		}

		public void selectionChanged(IAction action, ISelection selection) {
			fTb.selectionChanged(this, selection);
		}
		
	}

}
