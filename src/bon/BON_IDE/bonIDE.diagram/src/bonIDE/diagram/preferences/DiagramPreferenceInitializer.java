package bonIDE.diagram.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

/**
 * @generated
 */
public class DiagramPreferenceInitializer extends AbstractPreferenceInitializer {

	/**
	 * @generated
	 */
	public void initializeDefaultPreferences() {
		IPreferenceStore store = getPreferenceStore();
		bonIDE.diagram.preferences.DiagramGeneralPreferencePage.initDefaults(store);
		bonIDE.diagram.preferences.DiagramAppearancePreferencePage.initDefaults(store);
		bonIDE.diagram.preferences.DiagramConnectionsPreferencePage.initDefaults(store);
		bonIDE.diagram.preferences.DiagramPrintingPreferencePage.initDefaults(store);
		bonIDE.diagram.preferences.DiagramRulersAndGridPreferencePage.initDefaults(store);

	}

	/**
	 * @generated
	 */
	protected IPreferenceStore getPreferenceStore() {
		return bonIDE.diagram.part.BonideDiagramEditorPlugin.getInstance().getPreferenceStore();
	}
}
