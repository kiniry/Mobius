/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 *
 */

package escjava.plugin;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import pluginlib.OptionWidget;

/**
 * This class implements the property page for the 
 * ESC/Java2 plugin.
 * 
 * @author David R. Cok
 */
public class EscjavaProperties extends pluginlib.PropertyPage {
//
//	// FIXME - can we move these common widgets/options to the library
//	
//	/** The option button corresponding to Eclipse logging. */
//	static public OptionWidget.BooleanWidget logging = new OptionWidget.BooleanWidget(Options.logging);
//
//	/** The choice of using the console or System.out for logging */
//	static final public OptionWidget.BooleanWidget useConsole = new OptionWidget.BooleanWidget(Options.useConsole);
//	
//	/** The choice to send informational output to the log file as well */
//	static final public OptionWidget.BooleanWidget alsoLogInfo = new OptionWidget.BooleanWidget(Options.alsoLogInfo);
//	
//	/** This is the list of widgets in the JmlEclipse options section of the properties page */
//	final static public OptionWidget[] eclipseOptions =  new OptionWidget[]{
//			logging, useConsole, alsoLogInfo
//	};
//
//	/**
//	 * The Simplify executable to use (a value is required).
//	 */
//	static final public OptionWidget.FileWidget simplify = new OptionWidget.FileWidget(Options.simplify);
//	/**
//	 * The option button corresponding to the Quiet option,
//	 * but in the reverse sense.
//	 */
//	static final public OptionWidget.BooleanWidget quiet = new OptionWidget.BooleanWidget(Options.quiet);
//
//	/**
//	 * The option button corresponding to -typecheck, which does only
//	 * parsing and typechecking.
//	 */
//	static final public OptionWidget.BooleanWidget typeCheckOnly = new OptionWidget.BooleanWidget(Options.typeCheckOnly);
//
//	/**
//	 * The option button corresponding to -parsePlus,
//	 * which turns off warnings due to missing semicolons
//	 */
//	static final public OptionWidget.BooleanWidget parsePlus = new OptionWidget.BooleanWidget(Options.parsePlus);
//
//	/**
//	 * The option button corresponding to -noSemicolonWarnings,
//	 * which turns off warnings due to missing semicolons
//	 */
//	static final public OptionWidget.BooleanWidget noSemicolonWarnings = new OptionWidget.BooleanWidget(Options.noSemicolonWarnings);
//
//	/**
//	 * Enables caution as well as warning messages to be produced,
//	 * correpsonding to the inverse of the -nocaution option
//	 */
//	static final public OptionWidget.BooleanWidget cautionMessages = new OptionWidget.BooleanWidget(Options.cautionMessages);
//
//	/**
//	 * Enables counterexample information to be generated [-counterexample option]
//	 */
//	static final public OptionWidget.BooleanWidget counterexample = new OptionWidget.BooleanWidget(Options.counterexample);
//
//	/**
//	 * Enables counterexample information to be generated [-counterexample option]
//	 */
//	static final public OptionWidget.BooleanWidget suggest = new OptionWidget.BooleanWidget(Options.suggest);
//
//	/**
//	 * Enables checking for the use of impure methods in annotations [-checkPurity option]
//	 */
//	static final public OptionWidget.BooleanWidget checkPurity = new OptionWidget.BooleanWidget(Options.checkPurity);
//
//	/** The option widget corresponding to the choice of source
//	 *  version compatibility (Java 1.3 or Java 1.4) to be supported -
//	 *  this is essentially the interpretation to be applied to the
//	 *  assert keyword.
//	 */
//	static final protected OptionWidget.ChoiceWidget source = new OptionWidget.ChoiceWidget(Options.source);
//
//	/**
//	 * This allows the setting of the Esc/Java -ea, -da, -eajava, -eajml options.
//	 */
//	static final public OptionWidget.ChoiceWidget assertBehavior = new OptionWidget.ChoiceWidget(Options.assertBehavior);
//			
//	/**
//	 * An array of the EscJava option widgets.
//	 */
//	static final private OptionWidget[] widgets =
//		{   simplify, 
//			new OptionWidget.Label("Syntax and semantics checks"),
//			typeCheckOnly, 
//			noSemicolonWarnings, 
//			cautionMessages,
//			checkPurity,
//			new OptionWidget.Label("Generated information"),
//			counterexample,
//			suggest,
//			quiet,
//			new OptionWidget.Label("Java language"),
//			source, 
//			assertBehavior };
//	
//	/** This is an array of toggles that control which
//	 *  escjava warnings static checker warnings are
//	 *  enabled [-nowarn option]
//	 */
//	static private OptionWidget.BooleanWidget[] warningWidgets;
//
	/** Creates the property page controls and initializes them.
	 *  @param parent The UI object into which to insert the controls
	 *  @return The new control that is added to 'parent'
	 */
	protected Control createContents(Composite parent) {
		
		// Creates the contents of the property page view.
		
		Control composite = null; //addControl(parent);
		return composite;
	}
//	
//	
////	/**
////	 * This method is just a way to access to the underlying Eclipse project object.
////	 * 
////	 * @return The current underlying project
////	 */
////	private IProject getProject() {
////		return (IProject) getElement();
////	}
//
//	/**
//	 * Constructs the view of the property page by adding different features
//	 * like labels, and setting the layout. Just a helper to <code>createContents()
//	 * </code>.
//	 * 
//	 * @param parent The parent composite to which the controls are added
//	 * @return The resulting control that defined the looking of the property page
//	 */
//	private Control addControl(Composite parent) {
//		Composite composite0a = new Widgets.VComposite(parent);
//		new Label(composite0a, SWT.CENTER).setText("These options are workspace options that apply to every EscJava-enabled Java project.");
//		Composite composite0 = new Widgets.HComposite(composite0a,2);
//		Composite composite1 = new Widgets.VComposite(composite0);
//		Composite composite2a = new Widgets.VComposite(composite0);
//		new Widgets.LabeledSeparator(composite2a,"Static checks performed by Esc/Java");
//		Composite composite2 = new Widgets.HComposite(composite2a,2);
//		Composite composite3 = new Widgets.VComposite(composite2);
//		Composite composite4 = new Widgets.VComposite(composite2);
//
//		new Widgets.LabeledSeparator(composite1,"Options for Escjava-Eclipse");
//		addWidgets(eclipseOptions,composite1);
//		new Widgets.LabeledSeparator(composite1,"Options that control EscJava checking");
//		addWidgets(widgets,composite1);
//		
//
//		// FIXME - -quiet, nowarn noredundancy loop loopsafe  plainwarning pgc ppvc f pxLog  quiet sourcepath classpath specpath source
//
//		initWarningWidgets();
//		int n = warningWidgets.length;
//		addWidgets(warningWidgets,0,(n+1)/2,composite3);
//		addWidgets(warningWidgets,(n+1)/2,n-(n+1)/2,composite4);
//
//		return composite0;
//	}
//
//	/**
//	 * Creates and initializes the array of warning widgets
//	 */
//	private static void initWarningWidgets() {
//		AbstractOption.BooleanOption[] opts = Options.warningOptions();
//		int n = opts.length;
//		warningWidgets = new OptionWidget.BooleanWidget[n];
//
//		for (int i=0; i<n; ++i) {
//			warningWidgets[i] = new OptionWidget.BooleanWidget(opts[i]);
//		}	
//	}
//
//	/**
//	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
//	 */
//	public boolean performOk() {
//		// When OK is pressed, set all the options selected.	
//		setOptionValue(eclipseOptions);
//		AbstractOption.notifyListeners();
//		setOptionValue(widgets);
//		setOptionValue(warningWidgets);
//		return true;
//	}
//
//	public void performDefaults() {
//		// When OK is pressed, set all the options selected.	
//		setDefaults(eclipseOptions);
//		setDefaults(widgets);
//		setDefaults(warningWidgets);
//	}
//	
	public OptionWidget[] options() {
		// We don't use this since performOK and performDefaults
		// are both overridden
		throw new RuntimeException();
	}
//	
}