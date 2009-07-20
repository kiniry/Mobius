//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Languages.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages;

import jack.plugin.JackPlugin;
import jack.plugin.prove.ProofTask;
import jack.util.Logger;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.exceptions.LanguageException;
import jml2b.languages.java.JavaLanguage;
import jml2b.pog.IObviousProver;
import jml2b.pog.IProverStatus;
import jml2b.pog.lemma.ProverStatus;
import jml2b.pog.printers.IPrinter;
import jpov.IInteractiveProver;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;

/**
 * This class allows to register plugins into Jack.
 * 
 * @author L. Burdy
 **/
public class Languages {

	/**
	 * The number of registred plugins.
	 **/
	private static byte nbLanguages;

	/**
	 * The set of plugin names, it contains String. 
	 **/
	private static Vector languagesNames = new Vector();

	/**
	 * The set of plugin classes, those classes implement ILanguage.
	 **/
	private static Vector languagesClass = new Vector();

	/**
	 * The set of plugin translation result classes implementing ITranslationResult.
	 **/
	private static Vector translationResultClass = new Vector();

	/**
	 * The set of plugin printer classes implementing IPrinter.
	 **/
	private static Vector printerClass = new Vector();

	/**
	 * The set of plugin prover status classes extending ProverStatus.
	 **/
	private static Vector proverStatusClass = new Vector();

	/**
	 * The set of plugin interactive prover classes implementing IInteractiveProver.
	 **/
	private static Vector interactiveProverClass = new Vector();

	/**
	 * The set of plugin obvious prover classes implementing IObviousProver.
	 **/
	private static Vector obviousProverClass = new Vector();
	
	/**
	 * The set of plugin proof task classes extending ProofClass.
	 **/
	private static Vector proofTaskClass = new Vector();

	/**
	 * Static initializer that register plugins.
	 **/
	static {
		//TODO Peut-tre qu'il existe un autre endroit pour faire la registration des
		// plugins (voir le bouquin)
		new JavaLanguage();
		if (Platform.getExtensionRegistry() != null) {
			IExtensionPoint[] ipd = 
				Platform.getExtensionRegistry().getExtensionPoints();
			for (int i = 0; i < ipd.length; i++) {
				IExtension[] ie = ipd[i].getExtensions();
				for (int j = 0; j < ie.length; j++) {
					if (ie[j]
					       .getExtensionPointUniqueIdentifier()
					       .equals(JackPlugin.PROVER_EXTENSION_ID)) {
						IConfigurationElement[] ice =
							ie[j].getConfigurationElements();
						for (int k = 0; k < ice.length; k++) {
							if (ice[k].getName().equals("language"))
								try {
									ILanguage il =
										(
												ILanguage) ice[k]
												               .createExecutableExtension(
												               "languageClass");
									ITranslationResult it =
										(
												ITranslationResult) ice[k]
												                        .createExecutableExtension(
												                        "translationResultClass");
									IPrinter ip = null;
									try {
										ip =
											(
													IPrinter) ice[k]
													              .createExecutableExtension(
													              "printerClass");
									} catch (CoreException ce) {
										;
									}
									ProverStatus ps = null;
									try {
										ps =
											(
													ProverStatus) ice[k]
													                  .createExecutableExtension(
													                  "proverStatusClass");
									} catch (CoreException ce) {
										;
									}
									IInteractiveProver iip = null;
									try {
										iip =
											(
													IInteractiveProver) ice[k]
													                        .createExecutableExtension(
													                        "interactiveProverClass");
									} catch (CoreException ce) {
										;
									}
									IObviousProver iop = null;
									try {
										iop =
											(
													IObviousProver) ice[k]
													                    .createExecutableExtension(
													                    "obviousProverClass");
									} catch (CoreException ce) {
										;
									}
									ProofTask pt = null;
									try {
										pt =
											(
													ProofTask) ice[k]
													               .createExecutableExtension(
													               "proofTaskClass");
									} catch (CoreException ce) {
										;
									}
									register(
									         ice[k].getAttribute("name"),
									         il,
									         it,
									         ip,
									         ps,
									         iip,
									         iop,
									         pt);
								} catch (Exception ce) {
									Logger.err.println(ce.getMessage());
								}
						}
					}
				}
			}
		}
	}

	/**
	 * Register a plugin
	 * @param name The name
	 * @param il The language class
	 * @param rc The translation result class
	 * @param ip The printer class
	 * @param ps The prover status class
	 * @param iip The interactive prover class
	 * @param iop The obvious prover class
	 * @param pt  The proof task class
	 */
	public static void register(
		String name,
		ILanguage il,
		ITranslationResult rc,
		IPrinter ip,
		ProverStatus ps,
		IInteractiveProver iip,
		IObviousProver iop,
		ProofTask pt) {
		languagesNames.add(nbLanguages, name);
		languagesClass.add(nbLanguages, il);
		translationResultClass.add(nbLanguages, rc);
		printerClass.add(nbLanguages, ip);
		proverStatusClass.add(nbLanguages, ps);
		interactiveProverClass.add(nbLanguages, iip);
		obviousProverClass.add(nbLanguages, iop);
		proofTaskClass.add(nbLanguages++, pt);
	}

	/**
	 * Returns the language class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The language class associated  to the plugin.
	 * @throws LanguageException when the name is not a valid plugin name.
	 **/
	public static ILanguage getLanguageClass(String name)
		throws LanguageException {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			throw new LanguageException("Invalid language name: " + name);
		else
			return (ILanguage) languagesClass.get(index);
	}

	/**
	 * Returns the translation result class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The translation result class associated  to the plugin.
	 * @throws LanguageException when the name is not a valid plugin name.
	 **/
	public static ITranslationResult getTranslationResultClass(String name)
		throws LanguageException {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			throw new LanguageException("Invalid language name: " + name);
		else
			return (ITranslationResult) translationResultClass.get(index);
	}

	/**
	 * Returns the printer class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The printer class associated to the plugin or null if the name is not 
	 * a valid plugin name.
	 **/
	public static IPrinter getPrinterClass(String name) {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			return null;
		else
			return (IPrinter) printerClass.get(index);
	}

	/**
	 * Returns the index of a given plugin name.
	 * @param name The plugin name.
	 * @return the index in the set of plugins of the plugin name.
	 */
	public static int getIndex(String name) {
		return languagesNames.indexOf(name);
	}

	/**
	 * @return the number of registered plugins.
	 */
	public static byte getNbLanguages() {
		return nbLanguages;
	}

	/**
	 * @return the enumeration of languages name (String).
	 */
	public static Enumeration getLanguagesNames() {
		return languagesNames.elements();
	}

	/**
	 * Returns the prover status class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The prover status class associated to the plugin or null if the name 
	 * is not a valid plugin name.
	 **/
	public static IProverStatus getProverStatusClass(String name) {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			return null;
		else
			return (IProverStatus) proverStatusClass.get(index);
	}

	/**
	 * Returns the interactive prover class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The interactive prover class associated to the plugin or null if the 
	 * name is not a valid plugin name.
	 **/
	public static IInteractiveProver getInteractiveProverClass(String name) {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			return null;
		else
			return (IInteractiveProver) interactiveProverClass.get(index);
	}

	/**
	 * Returns the obvious prover class instance for a given plugin name.
	 * @param name The plugin name.
	 * @return The obvious prover class associated to the plugin or null if the name 
	 * is not a valid plugin name.
	 **/
	public static IObviousProver getObviousProverClass(String name) {
		int index = languagesNames.indexOf(name);
		if (index == -1)
			return null;
		else
			return (IObviousProver) obviousProverClass.get(index);
	}

	/**
	 * Returns the enumeration of proof task classes
	 * @return the enumeration of proof task instances (ProofTask).
	 */
	public static Enumeration getProofTaskClasses() {
		return proofTaskClass.elements();
	}


}
