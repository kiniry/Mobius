package beetlzplugin.preferences;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import beetlzplugin.Activator;
import beetlzplugin.popup.actions.Messages;

/**
 * Here we construct the prefernece page for Beetlz.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class BeetlzPreferencePage extends FieldEditorPreferencePage
implements IWorkbenchPreferencePage {

  /** Field on preference page. */
  private FileFieldEditor jmlFile;
  /** Field on preference page. */
  private FileFieldEditor userSettingFile;
  /** Field on preference page. */
  private DirectoryFieldEditor skeletonFile;
  /** Field on preference page. */
  private BooleanFieldEditor pureBonField;
  /** Field on preference page. */
  private BooleanFieldEditor nonNullField;
  /** Field on preference page. */
  private RadioGroupFieldEditor sourceField;
  /** Field on preference page. */
  private BooleanFieldEditor verboseField;
  /** Field on preference page. */
  private BooleanFieldEditor noJmlField;
  /** Field on preference page. */
  private BooleanFieldEditor noJavaField;
  /** Field on preference page. */
  private BooleanFieldEditor noErrorField;
  /** Field on preference page. */
  private BooleanFieldEditor noWarningField;
  /** Field on preference page. */
  private BooleanFieldEditor noBasicsField;

  /**
   * Create new page and set title.
   */
  public BeetlzPreferencePage() {
    super(GRID);
    setPreferenceStore(Activator.getDefault().getPreferenceStore());
    setDescription(Messages.getString("BeetlzPreferencePage.preferencesTitle")); //$NON-NLS-1$
  }

  /**
   * Create the fields.
   */
  @Override
  public void createFieldEditors() {
    jmlFile = new FileFieldEditor(PreferenceConstants.SPEC_PATH,
        Messages.getString("BeetlzPreferencePage.jmlSpecsFolder"),
        getFieldEditorParent()); //$NON-NLS-1$

    jmlFile.setEmptyStringAllowed(false);
    addField(jmlFile);

    userSettingFile = new FileFieldEditor(PreferenceConstants.USER_SETTING_PATH,
        Messages.getString("BeetlzPreferencePage.userSettingFile"),
        getFieldEditorParent()); //$NON-NLS-1$
    userSettingFile.setEmptyStringAllowed(true);
    addField(userSettingFile);

    skeletonFile = new DirectoryFieldEditor(PreferenceConstants.SKELETON_PATH,
        Messages.getString("BeetlzPreferencePage.directoryForSkeleton"),
        getFieldEditorParent()); //$NON-NLS-1$
    skeletonFile.setEmptyStringAllowed(true);
    addField(skeletonFile);

    sourceField = new RadioGroupFieldEditor( PreferenceConstants.SOURCE_OPTION,
        Messages.getString("BeetlzPreferencePage.sourceIs"), 1, //$NON-NLS-1$ 
        new String[][] { { Messages.getString("BeetlzPreferencePage.default"), //$NON-NLS-1$ 
          "default" }, //$NON-NLS-1$ 
      {"BON", "bon" }, { "Java", "java"} },  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
      getFieldEditorParent(), true);
    sourceField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(sourceField);

    nonNullField = new BooleanFieldEditor(PreferenceConstants.NULL_CHECK_OPTION,
        Messages.getString("BeetlzPreferencePage.dontCheckNullity"),
        getFieldEditorParent()); //$NON-NLS-1$
    nonNullField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(nonNullField);

    noJmlField = new BooleanFieldEditor(PreferenceConstants.USE_JML_OPTION,
        Messages.getString("BeetlzPreferencePage.useJml"),
        getFieldEditorParent()); //$NON-NLS-1$
    noJmlField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(noJmlField);

    noJavaField = new BooleanFieldEditor(PreferenceConstants.USE_JAVA_OPTION,
        Messages.getString("BeetlzPreferencePage.useJava"),
        getFieldEditorParent()); //$NON-NLS-1$
    noJavaField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(noJavaField);

    noErrorField = new BooleanFieldEditor(PreferenceConstants.PRINT_ERROR_OPTION,
        Messages.getString("BeetlzPreferencePage.printErrors"),
        getFieldEditorParent()); //$NON-NLS-1$
    noErrorField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(noErrorField);

    noWarningField = new BooleanFieldEditor(PreferenceConstants.PRINT_WARNING_OPTION,
        Messages.getString("BeetlzPreferencePage.printWarnings"),
        getFieldEditorParent()); //$NON-NLS-1$
    noWarningField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(noWarningField);

    pureBonField = new BooleanFieldEditor(PreferenceConstants.PURE_BON,
        Messages.getString("BeetlzPreferencePage.usePureBon"),
        getFieldEditorParent()); //$NON-NLS-1$
    pureBonField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(skeletonFile);

    verboseField = new BooleanFieldEditor(PreferenceConstants.VERBOSE_OPTION,
        Messages.getString("BeetlzPreferencePage.doDebugInfo"),
        getFieldEditorParent()); //$NON-NLS-1$
    verboseField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(verboseField);

    noBasicsField = new BooleanFieldEditor(PreferenceConstants.USE_BASICS_OPTION,
        Messages.getString("BeetlzPreferencePage.useBasics"),
        getFieldEditorParent()); //$NON-NLS-1$
    noBasicsField.fillIntoGrid(getFieldEditorParent(), 3);
    addField(noBasicsField);


  }

  /**
   * Create the contents.
   * @param parent composite
   */
  @Override
  protected Control createContents(final Composite parent) {
    final Composite fieldEditor = (Composite) super.createContents(parent);
    final GridLayout layout = new GridLayout();
    layout.numColumns = 3;
    layout.marginHeight = 0;
    layout.marginWidth = 0;
    fieldEditor.setLayout(layout);
    fieldEditor.setFont(parent.getFont());

    return fieldEditor;
  }

  /**
   * Adjust the layout or we have a huge page.
   */
  @Override
  protected void adjustGridLayout() {
    ((GridData) jmlFile.getTextControl(getFieldEditorParent()).
        getLayoutData()).horizontalSpan = 1;
    ((GridData) jmlFile.getTextControl(getFieldEditorParent()).getLayoutData()).widthHint = 20;
    ((GridData) userSettingFile.getTextControl(getFieldEditorParent()).
        getLayoutData()).widthHint = 20;
    ((GridData) userSettingFile.getTextControl(getFieldEditorParent()).
        getLayoutData()).horizontalSpan = 1;
    ((GridData) skeletonFile.getTextControl(getFieldEditorParent())
        .getLayoutData()).horizontalSpan = 1;
    ((GridData) skeletonFile.getTextControl(getFieldEditorParent()).
        getLayoutData()).widthHint = 20;
    
  }


  public void init(final IWorkbench workbench) {
  }

}