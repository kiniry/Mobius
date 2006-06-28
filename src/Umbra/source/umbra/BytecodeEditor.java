package umbra;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

/**
 * This is the main class defining the Bytecode Editor
 * as a subclass of TextEditor, which is a standard class
 * extended by each editor window.
 * Its specificities are additional attributes describing
 * BCEL structures related to the edited Bytecode
 * such as JavaClass to obtain particular instructions
 * and ClassGen to allow changes in BCEL.
 * 
 * @author BYTECODE team
 */

public class BytecodeEditor extends TextEditor {
	
	private ColorManager colorManager;
	private int mod;
	private boolean updated = true;
	private AbstractDecoratedTextEditor relatedEditor;
	private JavaClass javaClass;
	private ClassGen classGen;
	private int historyNum = -1;
	
	/**
	 * A constructor with no Bytecode-related specificity
	 */
	
	public BytecodeEditor() {
		super();
		mod = Composition.getMod();
		colorManager = new ColorManager();
		setSourceViewerConfiguration(new BytecodeConfiguration(colorManager, mod));
		setDocumentProvider(new BytecodeDocumentProvider());
	}
	
	/**
	 * Default function used while closing editor
	 */
	
	public void dispose() {
		colorManager.dispose();
		super.dispose();
	}
	
	public boolean isUpdated() {
		return updated;
	}
	
	public void leave() {
		updated = false;
	}
	
	/**
	 * @return Java code editor 
	 * that Bytecode has been generated from
	 */
	
	public AbstractDecoratedTextEditor getRelatedEditor() {
		return relatedEditor;
	}
	
	/**
	 * @return BCEL structure related to Bytecode
	 * that allows obtaining its particular instructions
	 */
	
	public JavaClass getJavaClass() {
		return javaClass;
	}
	
	/**
	 * This is a function executed directly after initialization
	 * that makes realtion to BCEL structures
	 * 
	 * @param editor	Java code editor with intended relation
	 * 					(used especially during synchronization)
	 * @param jc		BCEL structures that Bytecode has been
	 * 					generated from and may be modificated with
	 */
	public void setRelation(AbstractDecoratedTextEditor editor, JavaClass jc) {
		relatedEditor = editor;
		javaClass = jc;
		classGen = new ClassGen(javaClass);
		((BytecodeDocumentProvider)getDocumentProvider()).setRelation(editor, javaClass, classGen, getEditorInput());
	}
	
	/**
	 * This method is run automatically while standard Eclipse
	 * 'save' action is executed. Additionally to the usual
	 * editor saving, it also updates structure JavaClass in BCEL
	 * and binary files to allow Bytecode modifications being seen
	 * while executing. The original binary file is saved with the name
	 * with '_' at the beginning in case later rebuilding (if there has
	 * not existed such yet, the binary file is simply rewritten, otherwise
	 * it is saved unchanged). 
	 */
	
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
		IPath active = ((FileEditorInput)getEditorInput()).getFile().getFullPath();
		String fnameFrom = active.toOSString().replaceFirst(".btc", ".class");
		String lastSegment = active.lastSegment().replaceFirst(".btc", ".class");
		String fnameTo = active.removeLastSegments(1).append("_" + lastSegment).toOSString();
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot(); 
		IFile fileFrom = root.getFile(new Path(fnameFrom));
		IPath pathTo = new Path(fnameTo);
		IFile fileTo = root.getFile(pathTo);
		try {
			if (!fileTo.exists()) fileFrom.copy(pathTo, true, null);
		} catch (CoreException e1) {
			e1.printStackTrace();
		}
		try {
			JavaClass jc = classGen.getJavaClass();
			String path3 = getPath(active).append(lastSegment).toOSString(); 
			System.out.println("Path3: " + path3);
			jc.dump(path3);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * Transform relative file path (inside the project) into absolute
	 * 
	 * @param path		relative path
	 * @return			absolute path
	 */
	
	public IPath getPath(IPath path) {
		return ResourcesPlugin.getWorkspace().getRoot().getFolder(path).getProject().getLocation();
	}
	
	/**
	 * Generates input file from JavaClass structure
	 * and put it into the editor window.
	 * The input file is created literally from JavaClass
	 * code getting methods.
	 * Possibly comments can be inserted if they are given
	 * as a parameter (in the situation that they have been
	 * previously written).
	 * There is temporary limit of 256 signs for method name
	 * and 4096 signs for method code.
	 * 
	 * @param path			The relative path of the input file
	 * @param commentTab	Table of comments to be inserted
	 * @param interlineTab 	Table of comments between instructions to be also inserted
	 * @throws ClassNotFoundException
	 * @throws CoreException
	 * @throws IOException
	 */
	
	public void refreshBytecode(IPath path, String[] commentTab, String[] interlineTab) throws ClassNotFoundException, CoreException, IOException {
		String pathName = getPath(path).toOSString(); 	
		FileEditorInput input = (FileEditorInput)getEditorInput();
		IFile file = input.getFile();
		String clname = path.lastSegment().substring(0, path.lastSegment().lastIndexOf("."));
		ClassPath cp = new ClassPath(pathName);
		System.out.println("pathName = " + pathName);
		SyntheticRepository strin = SyntheticRepository.getInstance(cp);
		JavaClass jc = strin.loadClass(clname);
		strin.removeClass(jc);
		controlPrint(jc);
		Method[] methods = jc.getMethods();
		byte[][] names = new byte[methods.length][256];
		byte[][] code = new byte[methods.length][4096];
		int[] namesLen = new int[methods.length];
		int[] codeLen = new int[methods.length];
		int off = 0;
		for(int i = 0; i < methods.length; i++) {
			try {
				namesLen[i] = methods[i].toString().getBytes().length;
				names[i] = methods[i].toString().getBytes();
				codeLen[i] = methods[i].getCode().toString().length();
				String bareCode = methods[i].getCode().toString();
//				code[i] = addComment(bareCode, commentTab, off).getBytes();
				String c = addComment(bareCode, commentTab, interlineTab, off);
				code[i] = c.getBytes();
				codeLen[i] = c.length();
				off += getOffset(bareCode);
			} catch (NullPointerException e) {
				e.printStackTrace();
			}
		}
		byte[] contents = new byte[4096 * methods.length];
		for(int i = 0, k = 0; i < methods.length; i++) {
			for(int j = 0; j < namesLen[i]; j++, k++) {
				contents[k] = names[i][j];
			}
			contents[k] = '\n';
			k++;
			for(int j = 0; j < codeLen[i]; j++, k++) {
				contents[k] = code[i][j];
			}
			contents[k] = '\n';
			k++;
		}
		InputStream stream = new ByteArrayInputStream(contents);
		if (file.exists()) {
			file.setContents(stream, true, true, null);
		} else {
			file.create(stream, true, null);
		}
		stream.close();
		javaClass = jc;
	}
	
	/**
	 * Computes position of the next instruction line in the Bytecode method.
	 * 
	 * @param code	processing Bytecode method
	 * @param pos	index of a character in code
	 * @return		index of first ":" in the next instruction line.
	 */
	private int nextLineOff(String code, int pos) {
		// pozycja nastêpnego dwukropka
		boolean nline = false;
		int len = code.length();
		int res = -1;
		char c;
		for(;;) {
			if (pos >= len)
				break;
			c = code.charAt(pos);
			if ((c == ':') && (nline))
				break;
			if ((c < '0') || (c > '9'))
				nline = false;
			if (c == '\n') {
				nline = true;
				res = pos + 1;
			}
			pos++;
		};
		//if ((res >= len) || (res < 0)) System.out.println("the end");
		//else System.out.println("<" + code.charAt(res) + ">");
		return res;
	}
	
	/**
	 * Counts instructions in a Bytecode
	 * 
	 * @param bareCode	processing bytecode method
	 * @return		number of instructions in bareCode
	 */
	private int getOffset(String bareCode) {
		/* ile dwukropków? */
		int p = 0;
		int ile = 0;
		while (p >= 0) {
			p = nextLineOff(bareCode, p);
			ile++;
		};
		return ile - 1;
	}

	/**
	 * Adds comments to one Bytecode method.
	 * 
	 * @param bareCode		one method of the Bytecode (as a String with no comments)
	 * @param commentTab	array of comments (as Strings, without leading slashes)
	 * 						for each line of bytecode
	 * @param interlineTab 	array of comments between lines
	 * @param off			position of bareCode's first line's comment in commentTab
	 * @return				bareCode with inserted comments from commentTab
	 */
	private String addComment(String bareCode, String[] commentTab, String[] interlineTab, int off) {
		if ((commentTab == null) || (interlineTab == null)) return bareCode;
		int len = commentTab.length;
		if (interlineTab.length != len) return bareCode;
		int n = 0;
		String newCode = "";
		System.out.println("off=" + off);
		for(;;) {
			int i = nextLineOff(bareCode, 0);
			if (i == -1)
				i = bareCode.length() - 1;
			String line = bareCode.substring(0, i);
			System.out.println("line = <<" + line + ">>");
			bareCode = bareCode.substring(i, bareCode.length()) + " ";
			if (n + off - 1 >= len)
				break;
			if (n > 0){
				if (commentTab[n + off - 1] != null) {
					line = line.replaceFirst("\n", " //" + commentTab[n + off - 1] + "\n");
				}
				if ((interlineTab[n + off - 1] != null)
					&& (interlineTab[n + off - 1].compareTo("") != 0)) {
					line = "//" + interlineTab[n + off - 1] + "\n" + line;
				}
			}
			newCode = newCode + line;
			n++;
		};
		newCode += bareCode;
		return newCode;
	}

	/**
	 * Updating number of historical versions executed
	 * after adding new version
	 * 
	 * @return Current number of versions; 
	 * -1 if limit has been reached
	 */
	
	public int newHistory() {
		if (historyNum == IHistory.maxHistory) return -1;
		historyNum++;
		return historyNum;
	}
	
	/**
	 * Updating number of historical versions
	 * when all of them are removed.
	 */
	
	public void clearHistory() {
		historyNum = -1;
	}
	
	private void controlPrint(JavaClass jc) {
		System.out.println();
		System.out.println("Control print of instruction list:");
		ClassGen cg = new ClassGen(jc);
		ConstantPoolGen cpg = cg.getConstantPool();
		Method[] methods = cg.getMethods();
		MethodGen mg = new MethodGen(methods[1], cg.getClassName(), cpg);
		InstructionList il = mg.getInstructionList();
		InstructionHandle ih[] = il.getInstructionHandles();
		System.out.println("" + il.getLength() + " " + ih.length);
		for (int i = 0; i < il.getLength(); i++) {
			System.out.print("" + i + ". ");
			if (ih[i] == null) System.out.println("Null");
			else {
				System.out.println("(" + ih[i].getPosition() + ")");
				Instruction ins = ih[i].getInstruction();
				if (ins == null) System.out.println("Null instruction");
				else System.out.print(ins.getName());
				if (ih[i].getNext() == null) System.out.print(" next: null");
				else System.out.print(" next: " + ih[i].getNext().getPosition());
				if (ih[i].getPrev() == null) System.out.println(" prev: null");
				else System.out.println(" prev: " + ih[i].getPrev().getPosition());
			}
		}
	}
				
}
