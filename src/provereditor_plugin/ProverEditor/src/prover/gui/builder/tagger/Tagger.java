package prover.gui.builder.tagger;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import prover.Prover;


public class Tagger {
	/** The current selection in the workbench */
	public static final Tagger instance = new Tagger();
	
	public static final String filename = ".prover_editor_tags"; 
	private TagTable tags = new TagTable();
	private IProject fProject;
	
	public void run(IFile fResource) {
		
		if(fResource == null)
			return;
		if(fResource.getProject().equals(fProject)) {
			return;
		}
		
		loadTags(fProject);
		

	}
	
	
	public void loadTags(IProject project) {
		if(project.equals(fProject)) {
			return;
		}
		fProject = project;
		IFile file = project.getFile(filename);
		File tagfile = file.getRawLocation().toFile();
		if(file.exists()) {
			try {
				ObjectInputStream ois = new ObjectInputStream(new FileInputStream(tagfile));
				tags.load(ois);
				ois.close();
				
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		else {
			performFullBuild(project); 
		}		
	}
	public static void performCleanBuild(IProject project) {
		IFile file = project.getFile(filename);
		File tagfile = file.getRawLocation().toFile();
		tagfile.delete();
	}
	
	public void performAddChangedFile(IFile f) {
		IProject project = f.getProject();
		loadTags(project);
		try {
			tag(f.getRawLocation().toFile());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	public void performRemoveFile(IFile f) {
		IProject project = f.getProject();
		loadTags(project);
		tags.remove(f.getRawLocation().toFile().toString());
	}
	
	
	public void performFullBuild(IProject project) {
		File f = project.getLocation().toFile();
		tagDirectory(f);
		saveTags(project);	
	}


	private void saveTags(IProject project) {
		IFile file = project.getFile(filename);
		File tagfile = file.getRawLocation().toFile();
		try {
			ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(tagfile));
			tags.save(oos);
			oos.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	private void tagDirectory(File f) {
		File [] dirs = f.listFiles(new FileFilter(){
			public boolean accept(File pathname) {
				return pathname.isDirectory();
			}
		});
		File [] files = f.listFiles(new FileFilter(){
			public boolean accept(File pathname) {
				return pathname.getName().endsWith(".v");
			}
		});
		if(files != null)
			for(int i = 0; i < files.length; i++) {
				try {
					tag(files[i]);
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		if(dirs != null)
			for(int i = 0; i < dirs.length; i++) {
				tagDirectory(dirs[i]);
			}
	}


	private void tag(File file) throws IOException {
		Prover pr = Prover.findProverFromFile(file.toString());
		if(pr == null)
			return;
		Pattern[][] pats = pr.getTranslator().getTagPatterns();
		TagTable.TagList l = new TagTable.TagList();
		ProverFileReader lnr = new ProverFileReader(new FileReader(file));
		String str;
		int offset = 0;
		String filename = file.getAbsolutePath();
		while((str = lnr.readLine()) != null) {
			
			String old = str;
			for(int i = 0; i < pats.length; i++) {
				str = old;
				Matcher m = pats[i][0].matcher(str);
				if(m.find()) {
					int wordbeg = m.end() + offset;
					str = str.substring(m.end());
					m = pats[i][1].matcher(str);
					m.find();
					str = str.substring(0, m.end());
//					int wordend = m.end() + wordbeg;
					l.add(str, wordbeg, str.length(), filename);
					break;
				}
			}
			offset += lnr.getCount();
		}
		lnr.close();
		tags.add(filename,l);
	}


	public Iterator getTags() {
		return tags;
	}


	
}
