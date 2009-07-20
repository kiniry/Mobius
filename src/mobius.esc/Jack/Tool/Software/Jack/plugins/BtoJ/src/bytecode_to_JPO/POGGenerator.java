/*
 * Created on Jun 8, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bytecode_to_JPO;

import jack.plugin.JackPlugin;
import jack.util.Logger;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Vector;

import jml2b.pog.Pog;
import jml2b.pog.util.IdentifierResolver;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
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
import bytecode_wp.utils.Util;

/**
 * 
 * @author L. Burdy
 */
public class POGGenerator implements IRunnableWithProgress {

	private static final String TRANSLATION_TABLE_EXTENSION = ".trans";
	private static final  String BYTECODE_SOURCE_EXTENSION = ".cod";


	private String mchName = null;	
	private String absoluteName = null;
	private IProject project= null;
	private IResource resource=null;
	
	public POGGenerator() {}
	public POGGenerator(Object selection) {
		if(selection instanceof IFile) {
			init((IFile) selection);
		}
		else if (selection instanceof ICompilationUnit){
			init((ICompilationUnit) selection);
		}
		else {
			throw new IllegalArgumentException("Bad argument type: " + selection.getClass());
		}
	}
	private void init(ICompilationUnit icu) {
		IWorkbenchPart activePart = PlatformUI.getWorkbench()
		.getActiveWorkbenchWindow().getActivePage().getActivePart();
				IWorkbenchPartSite site = activePart.getSite();	
		project = icu.getJavaProject().getProject();
		
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
		resource = icu.getResource();
	}
	
	private void init(IFile file) {
		project = file.getProject();
		String directory = file.getProjectRelativePath().toFile()
				.getParentFile().getPath();
		directory = directory
				.substring(directory.indexOf(File.separator) + 1);
		String name = file.getName();
		mchName = name.substring(0, name.lastIndexOf('.'));
		absoluteName = directory + "." + mchName;
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
		
		try {
		

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
		
			monitor.subTask("Generating proof obligations");
			long startTime = System.currentTimeMillis();
			clazz.wp(config);
			
			long endTime = System.currentTimeMillis();
			Util.out.println("WP done " + ( endTime - startTime));
			try {
			IdentifierResolver.softInit(config);

			B2JClass bjc = null;

			Logger.warn.println("here");
			try {
			 bjc = ((B2JPackage) config.getPackage()).addB2JClass(
					config, clazz, true);
			}
			catch (Throwable e) {
				e.printStackTrace();
			}
				Logger.warn.println("here");
			
			bcjm = new BCJmlFile(bjc, mchName, config.getSubdirectory());

			Logger.warn.println("here");
			File bcSource = new File(config.getSubdirectory(), bcjm.getFlatName()
					+ BYTECODE_SOURCE_EXTENSION);
			Logger.warn.println("here");
			File translationTable = new File(config.getSubdirectory(), bcjm.getFlatName()
					+ TRANSLATION_TABLE_EXTENSION);

			Logger.warn.println("here");
			PrintStream sBcSource = new PrintStream(new FileOutputStream(bcSource));
			Logger.warn.println("here");
			ObjectOutputStream sTranslation = new ObjectOutputStream(new FileOutputStream(translationTable));
			HashMap hm = new HashMap();
			Logger.warn.println("here");
			bjc.saveCode(sBcSource, hm);
			Logger.warn.println("here");
			sTranslation.writeObject(hm);
			Logger.warn.println("here");
			sTranslation.close();
			sBcSource.close();
			Logger.warn.println("here");
			Pog.garbageIdent(bcjm);
			
			
			Pog.saveFiles(config, bcjm, monitor, new Vector(), new Vector(),
					new B2JClassResolver(config, (B2JPackage) config
							.getPackage(), clazz));
			if (resource != null) {
				try {
					resource.setPersistentProperty(
							JackPlugin.JPO_FROM_CLASS, 
							bcjm.getFlatName());
					resource.setPersistentProperty(
							JackPlugin.JML_BYTECODE_COMPILED,
							"true");
				} catch (CoreException ce) {
					Logger.err.println(ce);
				}
			}
			}
			catch (Throwable e) {
				e.printStackTrace();
				throw e;
			}
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
			// Logger.err.println(rea.getMessage());
		} catch (Exception e) {
			Logger.warn.println(e);
			e.printStackTrace();
		}
		catch (Throwable e) {
		}
		monitor.setCanceled(false);
		monitor.done();
		/*
		 * long endTime = System.currentTimeMillis(); long execTime = endTime -
		 * startTime; Logger.get().println("WP done " + execTime + "ms");
		 */
		
	}

	private static IPath getClassPath(IProject iproject) {
		// IFile icu = (IFile) selection.getFirstElement();
		IJavaProject project = JavaCore.create(iproject);

		// IClasspathEntry[] classPath = null;
		// IPath[] path = null;
		IPath out = null;
		try {
			out = project.getOutputLocation();
		} catch (JavaModelException e) {
			Logger.err.println(e);
		}

		return out;
	}
}