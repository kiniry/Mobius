package mobius.prover.gui;

import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import mobius.prover.Prover;
import mobius.prover.exec.AProverException;
import mobius.prover.exec.toplevel.TopLevel;
import mobius.prover.gui.editor.BasicRuleScanner;
import mobius.prover.gui.editor.LimitRuleScanner;
import mobius.prover.gui.jobs.AppendJob;
import mobius.prover.gui.jobs.ColorAppendJob;
import mobius.prover.gui.popup.AddToLoadPath;
import mobius.prover.gui.preference.PreferencePage;
import mobius.prover.plugins.AProverTranslator;
import mobius.prover.plugins.IProverTopLevel;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;


/**
 * The top level manager is the main class of the gui of ProverEditor.
 * It controls the top level, it glue the editor with the commands.
 * And it is a view part to show the current prover state.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TopLevelManager extends ABaseTopLevelManager  {
  /* Private fields: */
  /** the current TopLevelManager instance. */
  private static TopLevelManager instance;
  
  /* Instance fields: */
  /** the context associated with the current top level. */
  private ProverFileContext fProverContext = ProverFileContext.empty;
  /** the current running top level. */
  private TopLevel fTopLevel;
  /** the current prover running. */
  private Prover fProver;
  /** the translator currently used. */
  private AProverTranslator fTranslator;
  /** the parser used to parse the currently evaluated document. */
  private final BasicRuleScanner fParser = new BasicRuleScanner();

  /** the list of offset being the steps already taken by progress. */
  private Stack<Integer> fParsedList = new Stack<Integer>();

  /** the scanner used to color the text in the text viewer. */
  private BasicRuleScanner fStateScan;
  
  
  /**
   * Empty constructor. Creates an instance. There shall be only one
   * instance of the top level manager.
   */
  public TopLevelManager() {
    super();
    instance = this;
  }
  
  /**
   * Returns the current instance of the top level manager.
   * @return the last instance created of the top level manager.
   */
  public static TopLevelManager getInstance() {
    return instance;
  }
  
  /**
   * Tell whether or not we shall use unicode characters.
   * @return True if the unicode checkbox in the preferences is checked.
   */
  public static boolean isUnicodeMode() {
    return PreferencePage.getProverIsUnicode();
  }
  
  /**
   * Returns the parser for the current prover.
   * @return a parser to get the sentences.
   */
  public BasicRuleScanner getParser() {
    return fParser;
  }



  /**
   * Progress in the proof. If the progress was successful return true,
   * otherwise returns false.
   * @param pc the context in which to progress.
   * @return true if the progress was successful, false otherwise or if the
   *  lock was already set.
   */
  public boolean progress(final ProverFileContext pc) {
    if (!lock()) {
      return true;
    }
    boolean res;
    if (isNewDoc(pc)) {
      reset(pc);
      res = false;
    }
    else {
      final int oldlimit = pc.getLimit();
      res = progressIntern(pc, oldlimit, oldlimit);
    }
    unlock();
    return res;
  }
  
  /**
   * Progress in a proof.
   * @param pc the current context
   * @param realoldlimit the original old limit
   * @param oldlimit the current old limit
   * @return return true if no errors were found
   */
  private boolean progressIntern (final ProverFileContext pc, 
                                   final int realoldlimit, 
                                   final int oldlimit) { 
    final IDocument doc = pc.getDocument();
    fParser.setRange(doc, oldlimit, doc.getLength() - oldlimit);

    if (!findFirstSentence()) {
      return false;
    }
    
    final int newlimit = fParser.getTokenOffset() + fParser.getTokenLength() - 1;
    String cmd;
    try {
      cmd = doc.get(realoldlimit, newlimit - oldlimit).trim();
    } 
    catch (BadLocationException e) {
      // it should not happen
      System.err.println("TopLevel.progress_intern: " + e);
      return false;
    }
    
    // first we lock the evaluated part
    pc.setLimit(newlimit);
    final UpdateJob uj = new UpdateJob(pc.getPresentationReconciler(), 
                                       fProverContext, newlimit);
    uj.schedule();    
    return sendCommand(pc, realoldlimit, oldlimit, newlimit, cmd);
  }

  /**
   * Send the given command which is between real old limit 
   * and newlimit.
   * @param pc the context
   * @param realoldlimit the old limit
   * @param oldlimit the old limit in case of recursive call
   * @param newlimit the new limit
   * @param cmd the command to send
   * @return true if everything went fine
   */
  private boolean sendCommand(final ProverFileContext pc,
                              final int realoldlimit, final int oldlimit,
                              final int newlimit, 
                              final String cmd) {
    try {
      //we send the command
      switch (fProver.getTopLevelTranslator().hasToSkipSendCommand(fTopLevel, 
                                                                   pc.getDocument(), cmd, 
                                                                   oldlimit, newlimit)) {
        case IProverTopLevel.DONT_SKIP:
          fTopLevel.sendCommand(cmd);
          append(fTopLevel.getStdBuffer());
          if (fTopLevel.isAlive()) {
            fParsedList.push(new Integer(realoldlimit));
          }
          else {
            pc.setLimit(oldlimit);
            final UpdateJob up = new UpdateJob(pc.getPresentationReconciler(), 
                                               fProverContext, newlimit);
            up.schedule();
            return false;
          }
          break;
        case IProverTopLevel.SKIP_AND_CONTINUE:
          progressIntern(pc, realoldlimit, newlimit);
          break;
        case IProverTopLevel.SKIP:
        default:
          break;
      }
    } 
    catch (AProverException e) {
      pc.setLimit(realoldlimit);
      final UpdateJob uj = new UpdateJob(pc.getPresentationReconciler(), 
                                         fProverContext, newlimit);
      uj.schedule();
      final ColorAppendJob caj = new ColorAppendJob(getTxtPresentation(), e.toString(), RED);
      caj.prepare();
      return false;
    } 
    return true;
  }

  /**
   * Find the first sentence.
   * @return return true if we are not at the endoffile
   */
  private boolean findFirstSentence() {
    // first find the first sentence
    IToken tok;
    do {
      tok = fParser.nextToken();
    } while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
    if (tok.isEOF()) {
      return false;
    }
    return true;
  }
  


  /**
   * Regress in the proof. If the undo was successful returns true,
   * otherwise returns false.
   * @param pc the context in which to undo a command.
   * @return true if the undo was successful, false otherwise or if the
   *  lock was already set.
   */
  public boolean regress(final ProverFileContext pc) {
    if (!lock()) {
      return true;
    }
    boolean res;
    if (isNewDoc(pc)) {
      reset(pc);
      res = false;
    }
    else {
      res = regressIntern(pc);
    }
    unlock();
    return res;
  }  
  
  /**
   * 
   * @param pc the current context
   * @return true if everything went a'right
   */
  protected boolean regressIntern(final ProverFileContext pc) {
    final int oldlimit = pc.getLimit();
    if ((oldlimit > 0) && (fParsedList.size() > 0)) {
      final int newlimit = fParsedList.pop();
      String cmd;
      try {
        cmd = pc.getDocument().get(newlimit, oldlimit - newlimit).trim();
      } 
      catch (BadLocationException e) {
        // it should not happen
        System.err.println("TopLevel.regress_intern: " + e);
        return false;
      }
      final int hint = 
        fProver.getTopLevelTranslator().hasToSkipUndo(fTopLevel, pc.getDocument(), 
                                                      cmd, newlimit, oldlimit);
      switch(hint) {
        case IProverTopLevel.SKIP_AND_CONTINUE:
          pc.setLimit(newlimit);
          regressIntern(pc);
          break;
        case IProverTopLevel.DONT_SKIP: 
          try {
            fTopLevel.undo();
          } 
          catch (AProverException e) {
            append(e.toString());
          }
        case IProverTopLevel.SKIP: 
          pc.setLimit(newlimit);
        default:
          break;
      }
      
      final UpdateJob uj = new UpdateJob(pc.getPresentationReconciler(), 
                                         fProverContext, oldlimit + 1);
      uj.schedule();
    }
    return true;
  }
  
  
  /**
   * Reset the view, reset the toplevel, and set up everything.
   */
  private synchronized void reset() {
    if (fTopLevel != null) {
      fTopLevel.stop();
    }
    final IEditorInput input = fProverContext.getEditor().getEditorInput();
    
    final IFile path = (input instanceof IFileEditorInput) ? 
        ((IFileEditorInput) input).getFile() : null;
    fProver = Prover.findProverFromFile(path.getRawLocation().toString());
    fTranslator = fProver.getTranslator();
    fStateScan = new LimitRuleScanner(fTranslator.getProverStateRules());
    fParser.setRules(fTranslator.getParsingRules());
    
    new ColorAppendJob(getTxtPresentation(), "\nEditing file: " + 
                       path.getName() + ", \nUsing: " + fProver.getTop() + "\n", DARKRED).prepare();
    
    try {
      fTopLevel = new TopLevel(fProver.getName(), getLoadPath(path));
      //fTopLevel.addStandardStreamListener(this);
    } 
    catch (AProverException e) {
      new ColorAppendJob(getTxtPresentation(), e.toString(), RED).prepare();
    }
  
    // we reset the view
    fProverContext.setLimit(0);
    new UpdateJob(fProverContext.getPresentationReconciler(), 
                  fProverContext).schedule();
  }

  /**
   * Returns the load path for the given project, specified
   * by the path.
   * @param path the base path
   * @return a list of valid absolute path to add
   */
  private String[] getLoadPath(final IFile path) {
    String [] tab = null;    
    if (path != null) {      
      Set<String> hsPath;
      try {
        hsPath = AddToLoadPath.getAbsolutePaths(path.getProject());
      } 
      catch (IOException e) {
        hsPath = new HashSet<String>();
      }
      tab = new String[hsPath.size() + 2];
      tab [0] = path.getProject().getLocation().toString();
      tab [1] = path.getLocation().removeLastSegments(1).toString();
      final Iterator<String> iter = hsPath.iterator();
      for (int i = 2; i < tab.length; i++) {
        tab[i] = iter.next();
      }
    }
    return tab;
  }

  
  /**
   * Add the string given as an argument to the text viewer
   * used to show the state of the prover.
   * @param strToAppend The string to add to the text viewer of the prover.
   */
  public void append(final String strToAppend) {
    int ind = 0;
    String str = strToAppend;
    ind = str.indexOf("\n\n\n");
    if (ind != -1) {
      append(str.substring(0, ind));
      str = str.substring(ind);
    }
    
    final String [][] unicodeReplacements = fTranslator.getUnicodeReplacements();
    
    if (isUnicodeMode()) {
      for (int i = 0; i < unicodeReplacements.length; i++) {
        str = str.replaceAll(unicodeReplacements[i][0], 
            unicodeReplacements[i][1]);
      }
    }
    final String [][] replacements = fTranslator.getReplacements();
    for (int i = 0; i < replacements.length; i++) {
      str = str.replaceAll(replacements[i][0], 
          replacements[i][1]);
    }
    final AppendJob job = new AppendJob(fProverContext.getEditor(), 
                                        fStateScan, getTxtPresentation());
    
  
    job.add(str);
    job.prepare();
  }

  
  /**
   * Reset the top level and the view with the context
   * passed as a parameter.
   * @param pc The prover context which we have to
   * reset the view with
   */
  public void reset(final ProverFileContext pc) {
    if (pc.getDocument() != null) {
      fProverContext = pc;
      reset();
    }
  }

  /**
   * Tells whether or not the current doc
   * is the same as the doc in the context given as a parameter.
   * @param pc The context to test
   * @return true if the documents are different.
   */
  public boolean isNewDoc(final ProverFileContext pc) {
    return pc.getDocument() != fProverContext.getDocument();
  }



  /**
   * Tries to send a Ctrl-Break command to the prover.
   * @see mobius.prover.exec.ITopLevel#doBreak()
   */
  public void doBreak() {
    try {
      if (fTopLevel != null) {
        fTopLevel.doBreak();
      }
    } 
    catch (AProverException e) { 
      return;
    }
  }
  

 
}
