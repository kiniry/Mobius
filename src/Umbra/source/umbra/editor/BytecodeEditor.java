package umbra.editor;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;

import umbra.UmbraHelper;
import annot.bcclass.BCClass;
import annot.bcio.ReadAttributeException;

/**
 * This is the main class defining the Bytecode Editor
 * as a subclass of TextEditor, which is a standard class
 * extended by each editor window.
 * Its specificities are additional attributes describing
 * BCEL structures related to the edited Bytecode
 * such as JavaClass to obtain particular instructions
 * and ClassGen to allow changes in BCEL.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */

public class BytecodeEditor extends TextEditor {

  /**
   * The Java source code editor that corresponds to the current
   * bytecode editor.
   */
  private CompilationUnitEditor my_related_editor;


  /**
   * The BCEL structure which represents the bytecode the content of the
   * current editor has been generated from. They also serve to modify
   * the bytecode.
   */
  private JavaClass my_javaClass;

  /**
   * The BCEL structure to generate the bytecode file corresponding
   * to the {@link #my_javaClass}.
   */
  private ClassGen my_classGen;

  /**
   * This field contains the number of history items. This
   * field contains -1 when there are no active history
   * snapshots (i.e. the history is clear).
   */
  private int historyNum = -1;

  /**
   * The bytecode editor configuration manager associated with the current
   * editor.
   */
  private BytecodeConfiguration bconfig;

  /**
   * Bytecode document edited by the editor.
   */
  private BytecodeDocument currentDocument;

  /**
   * This constructor creates the class and initialises the default
   * color manager.
   */
  public BytecodeEditor() {
    super();
    bconfig = new BytecodeConfiguration();
    setSourceViewerConfiguration(bconfig);
    setDocumentProvider(new BytecodeDocumentProvider());
  }

  /**
   * Default function used while closing the current editor.
   */
  public final void dispose() {
    bconfig.disposeColor();
    super.dispose();
  }

  /**
   * @return Java code editor that Bytecode has been generated from
   */
  public final CompilationUnitEditor getRelatedEditor() {
    return my_related_editor;
  }

  /**
   * @return BCEL structure related to Bytecode
   * that allows obtaining its particular instructions
   */
  public final JavaClass getMy_javaClass() {
    return my_javaClass;
  }

  /**
   * This is a function executed directly after initialization
   * and it arranges the relation between the editor and BCEL structures.
   *
   * @param editor  Java code editor with intended relation
   *           (used in particular during synchronization)
   * @param jc    BCEL structures that Bytecode has been
   *           generated from and may be modificated with
   */
  public final void setRelation(final CompilationUnitEditor editor,
                                final JavaClass jc) {
    my_related_editor = editor;
    my_javaClass = jc;
    my_classGen = new ClassGen(jc);
    ((BytecodeDocumentProvider)getDocumentProvider()).
            setRelation(editor, this, getEditorInput());
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
  public final void doSave(final IProgressMonitor a_progress_monitor) {
    super.doSave(a_progress_monitor);
    final IPath active = ((FileEditorInput)getEditorInput()).getFile().getFullPath();
    final String fnameTo = UmbraHelper.getSavedClassFileNameForBTC(active);
    final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
    final String fnameFrom = active.toOSString().replaceFirst(
                UmbraHelper.BYTECODE_EXTENSION,
                UmbraHelper.CLASS_EXTENSION);
    final IFile fileFrom = root.getFile(new Path(fnameFrom));
    final IPath pathTo = new Path(fnameTo);
    final IFile fileTo = root.getFile(pathTo);
    try {
      if (!fileTo.exists()) fileFrom.copy(pathTo, true, null);
    } catch (CoreException e1) {
      e1.printStackTrace();
    }
    try {
      final JavaClass jc = my_classGen.getJavaClass();
      final String lastSegment = active.lastSegment().replaceFirst(
                  UmbraHelper.BYTECODE_EXTENSION,
                  UmbraHelper.CLASS_EXTENSION);
      final String path3 = getPath(active).append(lastSegment).toOSString();
      jc.dump(path3);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  /**
   * Transform relative file path (inside the project) into absolute
   *
   * @param path    relative path
   * @return      absolute path
   */
  public final IPath getPath(final IPath path) {
    return ResourcesPlugin.getWorkspace().getRoot().getFolder(path).getProject().getLocation();
  }

  /**
   * Generates input file from JavaClass structure
   * and puts it into the editor window.
   * The input file is created literally from JavaClass
   * code getting methods.
   * Possibly comments can be inserted if they are given
   * as a parameter (in the situation that they have been
   * previously written).
   * There is temporary limit of 256 characters for method name
   * and 4096 characters for method code.
   *
   * @param path      The relative path of the input file
   * @param comments  Table of comments to be inserted
   * @param interlineComments   Table of comments between instructions to be also inserted
   * @throws ClassNotFoundException
   * @throws CoreException
   * @throws IOException
   */
  public final void refreshBytecode(final IPath path,
                final String[] comments,
                final String[] interlineComments)
         throws ClassNotFoundException, CoreException, IOException {
    final String pathName = getPath(path).toOSString();
    final FileEditorInput input = (FileEditorInput)getEditorInput();
    final IFile file = input.getFile();

    // Get class name along with package name
    String clname = path.lastSegment().substring(0,
                       path.lastSegment().lastIndexOf("."));
    final String tmp = path.removeFirstSegments(1).toOSString();
    clname = tmp.substring(0, tmp.lastIndexOf("."));

    final ClassPath cp = new ClassPath(pathName);
    final SyntheticRepository strin = SyntheticRepository.getInstance(cp);
    final JavaClass jc = strin.loadClass(clname);
    strin.removeClass(jc);
    //controlPrint(jc);
//    ClassGen cg = new ClassGen(jc);
//    String clname2 = cg.getClassName();
//    ConstantPoolGen cpg = cg.getConstantPool();
//    Method[] methods = jc.getMethods();
//    byte[][] names = new byte[methods.length][256];
//    byte[][] code = new byte[methods.length][4096];
//    int[] namesLen = new int[methods.length];
//    int[] codeLen = new int[methods.length];
//    int off = 0;
    BCClass bcc;
    try {
      bcc = new BCClass(jc);
      final char[] bccode = bcc.printCode().toCharArray();
//      for(int i = 0; i < methods.length; i++) {
//        try {
//          namesLen[i] = methods[i].toString().getBytes().length;
//          names[i] = methods[i].toString().getBytes();
//          codeLen[i] = methods[i].getCode().toString().length();
//          String bareCode = methods[i].getCode().toString();
//          String c = addComment(bareCode, commentTab, interlineTab, off);
//          code[i] = c.getBytes();
//          codeLen[i] = c.length();
//          off += getOffset(bareCode);
//        } catch (NullPointerException e) {
//          e.printStackTrace();
//        }
//      }

      final byte[] contents = new byte[bccode.length];
      for(int i = 0; i < bccode.length; i++) {
        contents[i] = (byte) bccode[i];
//        for(int j = 0; j < namesLen[i]; j++, k++) {
//          contents[k] = names[i][j];
//        }
//        contents[k] = '\n';
//        k++;
//        for(int j = 0; j < codeLen[i]; j++, k++) {
//          contents[k] = code[i][j];
//        }
//        contents[k] = '\n';
//        k++;
      }
      final InputStream stream = new ByteArrayInputStream(contents);
      if (file.exists()) {
        file.setContents(stream, true, true, null);
      } else {
        file.create(stream, true, null);
      }
      stream.close();

    } catch (ReadAttributeException e1) {
      e1.printStackTrace();
    }

    my_javaClass = jc;
  }

//  private BCLocalVariable[] createLocalVariables(MethodGen m, ConstantPoolGen cpGen) {
//    LocalVariableGen[] locVarTable = m.getLocalVariables();
//    if (locVarTable == null) {
//      return null;
//    }
//    BCLocalVariable[] bclv = new BCLocalVariable[locVarTable.length];
//    for (int i = 0; i < locVarTable.length; i++) {
//      JavaType type = JavaType.getJavaType(locVarTable[i].getType());
//      BCLocalVariable lv = new BCLocalVariable(locVarTable[i]
//          .getLocalVariable(cpGen), type);
//      bclv[i] = lv;
//    }
//    return bclv;
//  }
//
//  private String addAnnot(Method method, ConstantPoolGen cpg, BCClass bcc, String cn) throws IOException, ReadAttributeException {
//    //System.out.println(method.getAttributes().length + " annotation(s):");
//    if (method.getAttributes().length > 1) {
//      Unknown att = (Unknown)method.getAttributes()[1];
////      System.out.println(att.getBytes().length);
////      System.out.println();
////      for (int i = 0; i < att.getBytes().length; i++) {
////        System.out.print(Integer.toHexString((att.getBytes()[i] + 256) % 256) + " ");
////      }
////      System.out.println();
//      MethodGen mg = new MethodGen(method, cn, cpg);
//      BCLocalVariable[] bclv = createLocalVariables(mg, cpg);
//      return AttributeReader.printAttribute(att, bcc, bclv);
//    }
//    return "";
//  }

//  /**
//   * Computes position of the next instruction line in the Bytecode method.
//   *
//   * @param code  processing Bytecode method
//   * @param pos  index of a character in code
//   * @return    index of first ":" in the next instruction line.
//   */
//  private int nextLineOff(String code, int pos) {
//    // pozycja nast�pnego dwukropka
//    boolean nline = false;
//    int len = code.length();
//    int res = -1;
//    char c;
//    for(;;) {
//      if (pos >= len)
//        break;
//      c = code.charAt(pos);
//      if ((c == ':') && (nline))
//        break;
//      if ((c < '0') || (c > '9'))
//        nline = false;
//      if (c == '\n') {
//        nline = true;
//        res = pos + 1;
//      }
//      pos++;
//    };
//    //if ((res >= len) || (res < 0)) System.out.println("the end");
//    //else System.out.println("<" + code.charAt(res) + ">");
//    return res;
//  }
//
//  /**
//   * Counts instructions in a Bytecode
//   *
//   * @param bareCode  processing bytecode method
//   * @return    number of instructions in bareCode
//   */
//  private int getOffset(String bareCode) {
//    /* ile dwukropk�w? */
//    int p = 0;
//    int ile = 0;
//    while (p >= 0) {
//      p = nextLineOff(bareCode, p);
//      ile++;
//    };
//    return ile - 1;
//  }
//
//  /**
//   * Adds comments to one Bytecode method.
//   *
//   * @param bareCode    one method of the Bytecode (as a String with no comments)
//   * @param commentTab  array of comments (as Strings, without leading slashes)
//   *             for each line of bytecode
//   * @param interlineTab   array of comments between lines
//   * @param off      position of bareCode's first line's comment in commentTab
//   * @return        bareCode with inserted comments from commentTab
//   */
//  private String addComment(String bareCode, String[] commentTab, String[] interlineTab, int off) {
//    if ((commentTab == null) || (interlineTab == null)) return bareCode;
//    int len = commentTab.length;
//    if (interlineTab.length != len) return bareCode;
//    int n = 0;
//    String newCode = "";
//    System.out.println("off=" + off);
//    for(;;) {
//      int i = nextLineOff(bareCode, 0);
//      if (i == -1)
//        i = bareCode.length() - 1;
//      String line = bareCode.substring(0, i);
//      System.out.println("line = <<" + line + ">>");
//      bareCode = bareCode.substring(i, bareCode.length()) + " ";
//      if (n + off - 1 >= len)
//        break;
//      if (n > 0){
//        if (commentTab[n + off - 1] != null) {
//          line = line.replaceFirst("\n", " //" + commentTab[n + off - 1] + "\n");
//        }
//        if ((interlineTab[n + off - 1] != null)
//          && (interlineTab[n + off - 1].compareTo("") != 0)) {
//          line = "//" + interlineTab[n + off - 1] + "\n" + line;
//        }
//      }
//      newCode = newCode + line;
//      n++;
//    };
//    newCode += bareCode;
//    return newCode;
//  }

  /**
   * Updating number of historical versions executed
   * after adding new version
   *
   * @return Current number of versions; -1 if limit has been reached
   */
  public final int newHistory() {
    if (historyNum == UmbraHelper.MAX_HISTORY) return -1;
    historyNum++;
    return historyNum;
  }

  /**
   * Updating number of historical versions
   * when all of them are removed.
   */
  public final void clearHistory() {
    historyNum = -1;
  }

  /**
   * @return the object which generates the class file
   */
  public final ClassGen getMy_classGen() {
    return my_classGen;
  }

  /**
   * This method sets the internal BCEL structures which contain the
   * information oabout the Java class.
   *
   * @param jc the Java class representation
   */
  public final void setMy_javaClass(final JavaClass jc) {
    my_javaClass = jc;
    my_classGen = new ClassGen(jc);
  }

  /**
   * @param document document to associate with the current editor
   */
  public final void setDocument(final BytecodeDocument document) {
    currentDocument = document;
  }

  /**
   * @return the currently edited document
   */
  public final BytecodeDocument getDocument() {
    return currentDocument;
  }

  /**
   * debugging helper
   *
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
  }*/
}
