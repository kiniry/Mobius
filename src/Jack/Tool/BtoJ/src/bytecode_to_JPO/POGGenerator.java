/*
 * Created on Jun 8, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bytecode_to_JPO;

import jack.plugin.JackPlugin;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.util.Vector;

import jml2b.pog.Pog;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PlatformUI;

import bytecode_wp.application.ClassPathMod;
import bytecode_wp.application.JavaClassLoader;
import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bytecode.block.IllegalLoopException;

/**
 * 
 * @author L. Burdy
 */
public class POGGenerator implements IRunnableWithProgress {

	Object firstElement;

	/**
	 * @param firstElement
	 */
	public POGGenerator(Object firstElement) {
		this.firstElement = firstElement;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.operation.IRunnableWithProgress#run(org.eclipse.core.runtime.IProgressMonitor)
	 */
	public void run(IProgressMonitor monitor) throws InvocationTargetException,
			InterruptedException {
		monitor.beginTask("Generating proof obligations",
				IProgressMonitor.UNKNOWN);
		IWorkbenchPart activePart = PlatformUI.getWorkbench()
				.getActiveWorkbenchWindow().getActivePage().getActivePart();
		IWorkbenchPartSite site = activePart.getSite();
		IProject project;
		String absoluteName;
		String mchName = null;
		if (firstElement instanceof ICompilationUnit) {
			ICompilationUnit icu = (ICompilationUnit) firstElement;
			project = icu.getJavaProject().getProject();
			// directory =
			// icu.getJavaProject().getProject().getProjectRelativePath().toFile().getParentFile().getPath();
			try {
				absoluteName = icu.getResource().getPersistentProperty(
						JackPlugin.ANNOTATED_CLASS);
			} catch (CoreException ce) {
				MessageDialog.openError(site.getShell(),
						JackPlugin.DIALOG_TITLE,
						"Error opening annotated class file: " + ce.toString());
				return;
			}
			if (absoluteName == null) {
				MessageDialog.openError(site.getShell(),
						JackPlugin.DIALOG_TITLE,
						"Class file has not been annotated.");
				return;
			}
			absoluteName = absoluteName.replace(File.separatorChar, '.');
			mchName = icu.getElementName().substring(0,
					icu.getElementName().indexOf('.'));
		} else {
			IFile icu = (IFile) firstElement;
			project = icu.getProject();
			String directory = icu.getProjectRelativePath().toFile()
					.getParentFile().getPath();
			directory = directory
					.substring(directory.indexOf(File.separator) + 1);
			String name = icu.getName();
			mchName = name.substring(0, name.lastIndexOf('.'));
			absoluteName = directory + "." + mchName;
		}

		B2JConfig config = new B2JConfig(project);

		ClassPathMod cl = new ClassPathMod(this.getClass().getClassLoader());

		String repos = config.getSubdirectory().getAbsolutePath();
		String outPut = project.getLocation().removeLastSegments(1).toString()
				+ getClassPath(project).toOSString();

		try {
			cl.addFile(repos + "/");
			cl.addFile(outPut + "/");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		monitor.subTask("Loading annotated class file");
		config.setJavaApplication(new B2JPackage(new JavaClassLoader(cl)));
		BCClass clazz = ((B2JPackage) config.getPackage())
				.getClass(absoluteName);
		BCJmlFile bcjm = null;
		try {
			monitor.subTask("Generating proof obligations");
			  long startTime = System.currentTimeMillis();
			clazz.wp(config);
			
			  long endTime = System.currentTimeMillis();
			  System.out.println("WP done " + ( endTime - startTime));
			// IdentifierResolver.init(config);
			B2JClass bjc = ((B2JPackage) config.getPackage()).addB2JClass(
					config, clazz, true);
			bcjm = new BCJmlFile(bjc, mchName, config.getSubdirectory());
			File fjpo = new File(config.getSubdirectory(), bcjm.getFlatName()
					+ ".cod");
			PrintStream pt = new PrintStream(new FileOutputStream(fjpo));
			bjc.saveCode(pt);
			pt.close();
			Pog.garbageIdent(bcjm);
			Pog.saveFiles(config, bcjm, monitor, new Vector(), new Vector(),
					new B2JClassResolver(config, (B2JPackage) config
							.getPackage(), clazz));

		} catch (RuntimeException e) {
			e.printStackTrace();
			MessageDialog.openInformation(site.getShell(),
					JackPlugin.DIALOG_TITLE, "PO Generate Error\n"
							+ e.getMessage() + " exc_type " + e.getClass());

		} catch (IllegalLoopException e) {
			MessageDialog.openInformation(site.getShell(),
					JackPlugin.DIALOG_TITLE, e.getMessage());
		} catch (ReadAttributeException e) {
			MessageDialog.openInformation(site.getShell(),
					JackPlugin.DIALOG_TITLE, e.getMessage());
		} catch (IOException e) {
			MessageDialog.openInformation(site.getShell(),
					JackPlugin.DIALOG_TITLE, e.getMessage());
			// } catch (Jml2bException rea) {
			// System.err.println(rea.getMessage());
		}
		if (firstElement instanceof ICompilationUnit) {
			ICompilationUnit icu = (ICompilationUnit) firstElement;
			if (bcjm != null)
				try {
					icu.getResource().setPersistentProperty(
							JackPlugin.JPO_FROM_CLASS, bcjm.getFlatName());
					icu.getResource().setPersistentProperty(
											JackPlugin.JML_BYTECODE_COMPILED,
											"true");
				} catch (CoreException ce) {

				}
		}
		monitor.setCanceled(false);
		monitor.done();
		/*
		 * long endTime = System.currentTimeMillis(); long execTime = endTime -
		 * startTime; System.out.println("WP done " + execTime + "ms");
		 */

	}

	public IPath getClassPath(IProject iproject) {
		// IFile icu = (IFile) selection.getFirstElement();
		IJavaProject project = JavaCore.create(iproject);

		// IClasspathEntry[] classPath = null;
		// IPath[] path = null;
		IPath out = null;
		try {
			out = project.getOutputLocation();
		} catch (JavaModelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return out;
	}
}