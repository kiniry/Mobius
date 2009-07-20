package mobius.prover;

import java.util.Hashtable;
import java.util.Map;

import mobius.prover.gui.editor.LimitRuleScanner;
import mobius.prover.gui.preference.ProverPreferenceNode;
import mobius.prover.plugins.AProverTranslator;
import mobius.prover.plugins.IProverTopLevel;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.PlatformUI;



/**
 * A prover is a class containing all the information given by
 * the plugins in a handy way. It is the basic object used to have
 * informations on the different plugins.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Prover {
  
  /** A set containing all the prover instances. */
  private static Map<String, Prover> fProverSet = 
    new Hashtable<String, Prover>();
  

  
  


  /** the name of the prover. */
  private String fName;
  
  /** the extension of the files of the prover. */
  private String fExtension;
  
  /** the preference page for the prover. */
  private ProverPreferenceNode fPreference;
  
  /** the translator class for the prover. */
  private AProverTranslator fTranslator;
  
  /** the translator class for the prover top level. */
  private IProverTopLevel fTopLevelTranslator;
  
  /**
   * Create an object representing a prover.
   * @param prefs the preference store
   * @param lang the language attribute of an 
   * extension point's configuration element if that sounds too obscur:
   * you know it is because a prover object shall not be created by
   * users outside ProverEditor.
   */
  public Prover (final IPreferenceStore prefs, 
                 final IConfigurationElement lang) {
    fName = lang.getAttribute("name");
    fExtension = lang.getAttribute("extension");
    try {
      fTranslator = (AProverTranslator) lang.createExecutableExtension("translator");
      fTopLevelTranslator = (IProverTopLevel) lang.createExecutableExtension("provertoplevel");
    } 
    catch (CoreException e) {
      e.printStackTrace();
    }
    
    final ProverPreferenceNode pn = new ProverPreferenceNode(fName, prefs);
    PlatformUI.getWorkbench().getPreferenceManager().addTo("ProverEditor.page",  pn);
    fPreference = pn;
    
    fProverSet.put(fName, this);
  }

  /**
   * Return the ide path as specified by the user.
   * @return A string containing the ide path
   */
  public String getIde() {
    return fPreference.getIde();
  }

  /**
   * Return the top level path as specified by the user.
   * @return A string containing the top level path
   */
  public String getTop() {
    return fPreference.getTop();
  }
  
  /**
   * Return the compiler path as specified by the user.
   * @return A string containing the compiler path
   */
  public String getCompiler() {
    return fPreference.getCompiler();
  }
  
  /**
   * Return the the grace time as specified by the user.
   * @return An integer to do a time out
   */
  public int getGraceTime() {
    return fPreference.getGraceTime();
  }
  
  /**
   * Returns the current instance of the translator 
   * associated with the prover.
   * @return The current translator
   */
  public AProverTranslator getTranslator() {
    return fTranslator;
  }
  
  /**
   * Return the current instance of the top level
   * translator associated with the prover.
   * @return The current top level translator
   */
  public IProverTopLevel getTopLevelTranslator() {
    return fTopLevelTranslator;
  }
  
  /**
   * Returns true if the name ends with the extension
   * of the prover.
   * @param str A string, not <code>null</code>
   * @return <code>true</code> if the parameter ends with
   * the prover's extension
   */
  private boolean extensionMatch(final String str) {
    return str.endsWith(fExtension);
  }

  /**
   * The scanner for the files.
   * @return A scanner to highlight the file in the editor
   */
  public LimitRuleScanner getRuleScanner() {    
    return new LimitRuleScanner(fTranslator.getProverTheoryRules());
  }
  
  /**
   * Returns the name of the prover.
   * <pre>
   * "A prover shall be called by its own name."
   * </pre>
   * @return the name of the prover 
   */
  public String getName() {
    return fName;
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    final String res = fName + " (" + fExtension + "): " + 
                       fTranslator + ", " + fPreference;
    return res;
  }

  /**
   * Tells whether or not the specified message is an
   * error message for the prover.
   * @param s the message to test
   * @return <code>true</code> if the message is an error message
   * as decide by the translator
   */
  public boolean isErrorMsg(final String s) {
    return fTranslator.isErrorMsg(s);
  }

  /**
   * Retrieve the prover whose name is specified.
   * @param language the name of the prover to get
   * @return a prover instance with the specified name or
   * <code>null</code> if none were found
   */
  public static Prover get(final String language) {
    return fProverSet.get(language);
  }
  
  /**
   * Retrieve the prover able to read the specified file.
   * @param str the file name to get the prover for
   * @return a prover instance able to read the file or
   * <code>null</code> if none were found
   */
  public static Prover findProverFromFile(final String str) {
    for (Prover p : fProverSet.values()) {
      if (p.extensionMatch(str)) {
        return p;
      }
    }
    
    return null;
  }  
}
