//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CompilationUnitDecorator.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.compile;

import jack.plugin.JackPlugin;
import jpov.Icons;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IDecoratorManager;

/**
 * Decorator allowing to add annotations to the name of the Java files.
 * @author A. Requet
 */
public class CompilationUnitDecorator
	extends LabelProvider
	implements ILightweightLabelDecorator {

	public static CompilationUnitDecorator getDemoDecorator() {
		IDecoratorManager decoratorManager =
			JackPlugin.getDefault().getWorkbench().getDecoratorManager();

		if (decoratorManager.getEnabled("jack.plugin.jmlcompileddecorator")) {
			return (
				CompilationUnitDecorator) decoratorManager
					.getBaseLabelProvider(
				"jack.plugin.jmlcompileddecorator");
		}
		return null;
	}

	public void decorate(Object object, IDecoration decoration) {

		IResource objectResource;

		if (object instanceof IResource) {
			objectResource = ((IResource) object);
		} else
			return;

		try {
			if (objectResource.getPersistentProperty(JackPlugin.JML_COMPILED)
				!= null
				&& objectResource.getPersistentProperty(
					JackPlugin.JML_COMPILED).equals(
					"true")) {
				decoration.addOverlay(Icons.COMPILED_DESCRIPTOR);
			}
		} catch (CoreException ce) {
			return;
		}
	}

	public static void refresh(IResource resourcesToBeUpdated) {

		CompilationUnitDecorator demoDecorator = getDemoDecorator();
		if (demoDecorator == null) {
			return;
		} else {
			// Fire a label provider changed event to decorate the 
			// resources whose image needs to be updated
			demoDecorator.fireLabelEvent(
				new LabelProviderChangedEvent(
					demoDecorator,
					resourcesToBeUpdated));
		}
	}

	private void fireLabelEvent(final LabelProviderChangedEvent event) {
		// We need to get the thread of execution to fire the label provider
		// changed event , else WSWB complains of thread exception. 
		Display.getDefault().asyncExec(new Runnable() {
			public void run() {
				fireLabelProviderChanged(event);
			}
		});
	}

}
