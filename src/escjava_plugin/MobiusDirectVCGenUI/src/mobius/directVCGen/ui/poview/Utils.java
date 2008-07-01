package mobius.directVCGen.ui.poview;

import java.net.URL;

import mobius.directVCGen.ui.poview.tree.WorkspaceElement;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.progress.UIJob;
import org.osgi.framework.Bundle;


public class Utils {
	private static Image imgGoal = null;
	private static Image imgLib = null;
	/**
	 * Returns a standard ok status.
	 * @return A standard ok status.
	 */
	public static IStatus getOkStatus() {
		return new Status(IStatus.OK, Activator.PLUGIN_ID, IStatus.OK, "", null);
	}
	
	public static Image createImage(String file) {
		Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
		IPath path = new Path(file);
		URL iconURL = FileLocator.find(bundle,path,null);
		return ImageDescriptor.createFromURL(iconURL).createImage();
	}
	
	public static void refreshTree(TreeViewer viewer, WorkspaceElement goal) {
		UIJob job = new RefreshJob(viewer, goal);
		job.schedule();
	}
	
	private static class RefreshJob extends UIJob {
		TreeViewer viewer;
		WorkspaceElement goal;
		public RefreshJob(TreeViewer viewer, WorkspaceElement goal) {
			super("Updating view");
			this.viewer = viewer;
			this.goal = goal;
		}

		public IStatus runInUIThread(IProgressMonitor monitor) {
			viewer.refresh(goal);
			return Utils.getOkStatus();

		}	
	}
	
	public static Image getPlatformImage(String id) {
		return PlatformUI.getWorkbench().getSharedImages().getImage(id);
	}
	public static Image getJdtImage(String id) {
		return JavaUI.getSharedImages().getImage(id);
	}

	public static Image getImage(int cst) {
		
		switch(cst) {
			case IImagesConstants.IMG_PROJECT:
				return getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT);
			case IImagesConstants.IMG_PROJECT_EMPTY:
				return getPlatformImage(IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED);
			case IImagesConstants.IMG_CLASS:
				return getJdtImage(ISharedImages.IMG_OBJS_CLASS);
			case IImagesConstants.IMG_METHOD:
				return getJdtImage(ISharedImages.IMG_OBJS_PRIVATE);
			case IImagesConstants.IMG_GOAL_SOLVED:
				return Utils.getJdtImage(ISharedImages.IMG_OBJS_PUBLIC);
			case IImagesConstants.IMG_GOAL:
				if (imgGoal == null) {
					imgGoal = createImage("icons/escjava_problem.gif");
				}
				return imgGoal;
			case IImagesConstants.IMG_LIB:
				if (imgLib == null) {
					imgLib = createImage("icons/coq.gif");
				}
				return imgLib;
			case IImagesConstants.IMG_DEFAULT:
			default:
				return getPlatformImage(org.eclipse.ui.ISharedImages.IMG_OBJ_ELEMENT);

		}
	}
	
	public static IProject [] getProjects() {
		return ResourcesPlugin.getWorkspace().getRoot().getProjects();
	}
}
