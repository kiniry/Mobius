/*
 * This file is part of the Esc/Java2 plugin project. Copyright 2004-2005 David
 * R. Cok
 * 
 * Created on Feb 2, 2005
 */
package escjava.plugin;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;

import pluginlib.AbstractPreference;
import pluginlib.PreferenceWidget;
import pluginlib.Widgets;

/**
 * @author David Cok
 * 
 * This class implements the preference page for the plugin
 */
public class PreferencePage extends pluginlib.PreferencePage {

  // FIXME - can we move these common widgets/options to the library

  /** The option button corresponding to Eclipse logging. */
  static public PreferenceWidget.BooleanWidget logging = new PreferenceWidget.BooleanWidget(
      Options.logging);

  /** The choice of using the console or System.out for logging */
  static final public PreferenceWidget.BooleanWidget useConsole = new PreferenceWidget.BooleanWidget(
      Options.useConsole);

  /** The choice to send informational output to the log file as well */
  static final public PreferenceWidget.BooleanWidget alsoLogInfo = new PreferenceWidget.BooleanWidget(
      Options.alsoLogInfo);

  /**
   * This is the list of widgets in the JmlEclipse options section of the
   * properties page
   */
  final static public PreferenceWidget[] eclipseOptions = new PreferenceWidget[] {
                                                                          logging,
                                                                          useConsole,
                                                                          alsoLogInfo };

  /**
   * The Simplify executable to use (a value is required).
   */
  static final public PreferenceWidget.FileWidget simplify = new PreferenceWidget.FileWidget(
      Options.simplify);

  /**
   * The option button corresponding to the Quiet option, but in the reverse
   * sense.
   */
  static final public PreferenceWidget.BooleanWidget quiet = new PreferenceWidget.BooleanWidget(
      Options.quiet);

  /**
   * The option button corresponding to -typecheck, which does only parsing and
   * typechecking.
   */
  static final public PreferenceWidget.BooleanWidget typeCheckOnly = new PreferenceWidget.BooleanWidget(
      Options.typeCheckOnly);

  /**
   * The option button corresponding to -parsePlus, which turns off warnings due
   * to missing semicolons
   */
  static final public PreferenceWidget.BooleanWidget parsePlus = new PreferenceWidget.BooleanWidget(
      Options.parsePlus);

  /**
   * The option button corresponding to -noSemicolonWarnings, which turns off
   * warnings due to missing semicolons
   */
  static final public PreferenceWidget.BooleanWidget noSemicolonWarnings = new PreferenceWidget.BooleanWidget(
      Options.noSemicolonWarnings);

  /**
   * Enables caution as well as warning messages to be produced, correpsonding
   * to the inverse of the -nocaution option
   */
  static final public PreferenceWidget.BooleanWidget cautionMessages = new PreferenceWidget.BooleanWidget(
      Options.cautionMessages);

  /**
   * Enables counterexample information to be generated [-counterexample option]
   */
  static final public PreferenceWidget.BooleanWidget counterexample = new PreferenceWidget.BooleanWidget(
      Options.counterexample);

  /**
   * Enables counterexample information to be generated [-counterexample option]
   */
  static final public PreferenceWidget.BooleanWidget suggest = new PreferenceWidget.BooleanWidget(
      Options.suggest);

  /**
   * Enables checking for the use of impure methods in annotations [-checkPurity
   * option]
   */
  static final public PreferenceWidget.BooleanWidget checkPurity = new PreferenceWidget.BooleanWidget(
      Options.checkPurity);

  /**
   * The option widget corresponding to the choice of source version
   * compatibility (Java 1.3 or Java 1.4) to be supported - this is essentially
   * the interpretation to be applied to the assert keyword.
   */
  static final protected PreferenceWidget.ChoiceWidget source = new PreferenceWidget.ChoiceWidget(
      Options.source);

  /**
   * This allows the setting of the Esc/Java -ea, -da, -eajava, -eajml options.
   */
  static final public PreferenceWidget.ChoiceWidget assertBehavior = new PreferenceWidget.ChoiceWidget(
      Options.assertBehavior);

  /**
   * An array of the EscJava option widgets.
   */
  static final private PreferenceWidget[] widgets = {
                                                 simplify,
                                                 new PreferenceWidget.Label(
                                                     "Syntax and semantics checks"),
                                                 typeCheckOnly,
                                                 noSemicolonWarnings,
                                                 cautionMessages,
                                                 checkPurity,
                                                 new PreferenceWidget.Label(
                                                     "Generated information"),
                                                 counterexample,
                                                 suggest,
                                                 quiet,
                                                 new PreferenceWidget.Label(
                                                     "Java language"), source,
                                                 assertBehavior };

  /**
   * This is an array of toggles that control which escjava warnings static
   * checker warnings are enabled [-nowarn option]
   */
  static private PreferenceWidget.BooleanWidget[] warningWidgets;

  /**
   * Creates the property page controls and initializes them.
   * 
   * @param parent The UI object into which to insert the controls
   * @return The new control that is added to 'parent'
   */
  protected Control createContents(Composite parent) {

    // Creates the contents of the property page view.

    Control composite = addControl(parent);
    return composite;
  }

  /**
   * Constructs the view of the property page by adding different features like
   * labels, and setting the layout. Just a helper to <code>createContents()
   * </code>.
   * 
   * @param parent The parent composite to which the controls are added
   * @return The resulting control that defined the looking of the property page
   */
  private Control addControl(Composite parent) {
    Composite composite0a = new Widgets.VComposite(parent);
    new Label(composite0a, SWT.CENTER)
        .setText("These options are workspace options that apply to every Esc/Java2-enabled Java project.");
    Composite composite0 = new Widgets.HComposite(composite0a, 2);
    Composite composite1 = new Widgets.VComposite(composite0);
    Composite composite2a = new Widgets.VComposite(composite0);
    new Widgets.LabeledSeparator(composite2a,
        "Static checks performed by Esc/Java2");
    Composite composite2 = new Widgets.HComposite(composite2a, 2);
    Composite composite3 = new Widgets.VComposite(composite2);
    Composite composite4 = new Widgets.VComposite(composite2);

    new Widgets.LabeledSeparator(composite1, "Options for Esc/Java2-Eclipse");
    addWidgets(eclipseOptions, composite1);
    new Widgets.LabeledSeparator(composite1,
        "Options that control Esc/Java2 checking");
    addWidgets(widgets, composite1);

    // FIXME - -quiet, nowarn noredundancy loop loopsafe plainwarning pgc ppvc f
    // pxLog quiet sourcepath classpath specpath source

    initWarningWidgets();
    int n = warningWidgets.length;
    addWidgets(warningWidgets, 0, (n + 1) / 2, composite3);
    addWidgets(warningWidgets, (n + 1) / 2, n - (n + 1) / 2, composite4);

    return composite0;
  }

  /**
   * Creates and initializes the array of warning widgets
   */
  private static void initWarningWidgets() {
    AbstractPreference.BooleanOption[] opts = Options.warningOptions();
    int n = opts.length;
    warningWidgets = new PreferenceWidget.BooleanWidget[n];

    for (int i = 0; i < n; ++i) {
      warningWidgets[i] = new PreferenceWidget.BooleanWidget(opts[i]);
    }
  }

  /**
   * @see org.eclipse.jface.preference.IPreferencePage#performOk()
   */
  public boolean performOk() {
    // When OK is pressed, set all the options selected.
    setOptionValue(eclipseOptions);
    AbstractPreference.notifyListeners();
    setOptionValue(widgets);
    setOptionValue(warningWidgets);
    return true;
  }

  public void performDefaults() {
    // When OK is pressed, set all the options selected.	
    setDefaults(eclipseOptions);
    setDefaults(widgets);
    setDefaults(warningWidgets);
  }

  /** Returns the array of widgets displayed in this page.
   * @return The array of PreferenceWidget objects for this page.
   */
  protected PreferenceWidget[] options() {
    throw new RuntimeException(); // SHOULD NOT BE USED
  }

  // Inherited method
  protected IPreferenceStore doGetPreferenceStore() {
    return EscjavaPlugin.getPlugin().getPreferenceStore();
  }

  /* (non-Javadoc)
   * @see org.eclipse.jface.dialogs.IDialogPage#performHelp()
   */
  public void performHelp() {}

  {
    pluginlib.AbstractPreference.preferenceStore = EscjavaPlugin
        .getPlugin().getPreferenceStore();
  }
}