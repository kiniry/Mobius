/*
 * This file is part of the ESC/Java2 plugin project. 
 * Copyright 2004-2005 David R. Cok
 * 
 * Modified 2007-2008 by Dermot Cochran for Mobius IST-15905
 * 
 * Created on Feb 2, 2005
 */
package escjava.plugin;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import mobius.util.plugin.APreference;
import mobius.util.plugin.APreference.BooleanOption;
import mobius.util.plugin.widgets.APreferencePage;
import mobius.util.plugin.widgets.APreferenceWidget;
import mobius.util.plugin.widgets.Widgets;
import mobius.util.plugin.widgets.APreferenceWidget.BooleanWidget;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;


/**
 * @author David Cok
 * 
 * This class implements the preference page for the plugin
 */
public class PreferencePage extends APreferencePage {
 

  /**
   * The option button corresponding to the Quiet option, but in the reverse
   * sense.
   */
  public static final APreferenceWidget.BooleanWidget quiet = 
    new APreferenceWidget.BooleanWidget(Options.quiet);

  /**
   * The option button corresponding to -typecheck, which does only parsing and
   * typechecking.
   */
  public static final APreferenceWidget.BooleanWidget typeCheckOnly = 
    new APreferenceWidget.BooleanWidget(Options.typeCheckOnly);

  /**
   * The option button corresponding to -parsePlus, which turns off warnings due
   * to missing semicolons.
   */
  public static final APreferenceWidget.BooleanWidget parsePlus = 
    new APreferenceWidget.BooleanWidget(Options.parsePlus);

  /**
   * The option button corresponding to -noSemicolonWarnings, which turns off
   * warnings due to missing semicolons.
   */
  public static final APreferenceWidget.BooleanWidget noSemicolonWarnings = 
    new APreferenceWidget.BooleanWidget(Options.noSemicolonWarnings);

  /**
   * Enables caution as well as warning messages to be produced, corresponding
   * to the inverse of the -nocaution option.
   */
  public static final APreferenceWidget.BooleanWidget cautionMessages = 
    new APreferenceWidget.BooleanWidget(Options.cautionMessages);

  /**
   * Enables counterexample information to be generated [-counterexample option].
   */
  public static final APreferenceWidget.BooleanWidget counterexample = 
    new APreferenceWidget.BooleanWidget(Options.counterexample);

  /**
   * Enables counterexample information to be generated [-counterexample option].
   */
  public static final APreferenceWidget.BooleanWidget suggest = 
    new APreferenceWidget.BooleanWidget(Options.suggest);

  /**
   * Enables checking for the use of impure methods in annotations [-checkPurity
   * option].
   */
  public static final APreferenceWidget.BooleanWidget checkPurity = 
    new APreferenceWidget.BooleanWidget(Options.checkPurity);

  /**
   * This allows the setting of the ESC/Java -ea, -da, -eajava, -eajml options.
   */
  public static final APreferenceWidget.ChoiceWidget assertBehavior = 
    new APreferenceWidget.ChoiceWidget(Options.assertBehavior);

  /**
   * This is an array of toggles that control which escjava warnings static
   * checker warnings are enabled [-nowarn option].
   */
  public static final List<BooleanWidget> warningWidgets = 
    new ArrayList<BooleanWidget>();
  
  /**
   * The option widget corresponding to the choice of source version
   * compatibility (Java 1.3, Java 1.4 or Java Card 2.1) to be supported.  
   */
  protected static final APreferenceWidget.ChoiceWidget source = 
    new APreferenceWidget.ChoiceWidget(Options.source);


  
  /**
   * An array of the ESCJava option widgets.
   */
  private static final List<APreferenceWidget<?>> widgets =
    new ArrayList<APreferenceWidget<?>>();
  static {
    final APreferenceWidget<?>[] tab = {
      new APreferenceWidget.Label("Syntax and semantics checks"),
      typeCheckOnly, noSemicolonWarnings, cautionMessages,
      checkPurity, new APreferenceWidget.Label("Generated information"),
      counterexample, suggest, quiet,
      new APreferenceWidget.Label("Java language"), source,
      assertBehavior };
    for (APreferenceWidget<?> w: tab) {
      widgets.add(w);
    }
  }

  /**
   * Creates the property page controls and initializes them.
   * 
   * @param parent The UI object into which to insert the controls
   * @return The new control that is added to 'parent'
   */
  protected Control createContents(final Composite parent) {

    // Creates the contents of the property page view.

    final Control composite = addControl(parent);
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
  private Control addControl(final Composite parent) {
    final Composite composite0a = new Widgets.VComposite(parent);
    new Label(composite0a, SWT.CENTER)
        .setText("These options are workspace options that apply to " +
            "every ESC/Java2-enabled Java project.");
    final Composite composite0 = new Widgets.HComposite(composite0a, 2);
    final Composite composite1 = new Widgets.VComposite(composite0);
    final Composite composite2a = new Widgets.VComposite(composite0);
    new Widgets.LabeledSeparator(composite2a,
        "Static checks performed by ESC/Java2");
    final Composite composite2 = new Widgets.HComposite(composite2a, 2);
    final Composite composite3 = new Widgets.VComposite(composite2);
    final Composite composite4 = new Widgets.VComposite(composite2);

    new Widgets.LabeledSeparator(composite1, "Options for ESC/Java2-Eclipse");
    addWidgets(eclipseOptions, composite1);
    addWidgets(widgets, composite1);
    
    // FIXME - -quiet, nowarn noredundancy loop loopsafe plainwarning pgc ppvc f
    // pxLog quiet sourcepath classpath specpath source

    initWarningWidgets();
    final int n = warningWidgets.size();
    addWidgets(warningWidgets, 0, (n + 1) / 2, composite3);
    addWidgets(warningWidgets, (n + 1) / 2, n - (n + 1) / 2, composite4);

    return composite0;
  }

  /**
   * Creates and initializes the array of warning widgets.
   * 
   * @requires Options.waningOptions() != null;
   */
  private static void initWarningWidgets() {
    final BooleanOption[] opts = Options.warningOptions();
    final int n = opts.length;
    warningWidgets.clear();

    for (int i = 0; i < n; ++i) {
      warningWidgets.add(new APreferenceWidget.BooleanWidget(opts[i]));
    }
  }

  /** {@inheritDoc} */
  public boolean performOk() {
    // When OK is pressed, set all the options selected.
    setOptionValue(eclipseOptions);
    APreference.notifyListeners();
    setOptionValue(widgets);
    setOptionValue(warningWidgets);
    return true;
  }
  
  /** {@inheritDoc} */
  public void performDefaults() {
    // When OK is pressed, set all the options selected.  
    setDefaults(eclipseOptions);
    setDefaults(widgets);
    setDefaults(warningWidgets);
  }

  /** Returns the array of widgets displayed in this page.
   * @return The array of PreferenceWidget objects for this page.
   */
  protected Collection<APreferenceWidget<?>> options() {
    throw new RuntimeException(); // SHOULD NOT BE USED
  }

  // Inherited method
  /** {@inheritDoc} */
  protected IPreferenceStore doGetPreferenceStore() {
    return EscjavaPlugin.getPlugin().getPreferenceStore();
  }

  /** {@inheritDoc} */
  public void performHelp() { }
}
