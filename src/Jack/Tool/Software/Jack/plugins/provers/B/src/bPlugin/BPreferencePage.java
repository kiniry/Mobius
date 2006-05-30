//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author L. Burdy
 **/
public class BPreferencePage
	extends PreferencePage
	implements IWorkbenchPreferencePage {

	public static final int VersionB4free = 0;
	public static final int Version36 = 1;
	public static final int Version35 = 2;
	
	
	Button remoteAtelierB;
	Button localB4Free;
	Label urlL;
	Text urlT;
	
	Label bbatchL;
	Text bbatchT;
	Button bbatchB;
	
	Label ressourceL;
	Text ressourceT;
	Button ressourceB;
	
	Label bdpL;
	Text bdpT;
	Button bdpB;
	
	Button versionB4Free20;
	Button version36;
	Button version35;
	
	Label abDefL;
	Text abDefT;
	Button abDefB;

	Label clickNProveL;
	Text clickNProveT;
	Button clickNProveB;
	
	boolean useRemoteAtelier;
	String urlS;
	String bbatchS;
	String ressourceS;
	String bdpS;
	int version;
	String abDefS;
	String clickNProveS;
	
	/**
	 * Creates the JackPreferencePage for provers settings.
	 *//*
	public BPreferencePage() {
		super(GRID);
		setPreferenceStore(BPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the Atelier B prover");

	}
*/
    protected Control createContents(Composite parent) {
 
    Composite composite = createComposite(parent);

//    Font font = composite.getFont();

    Group buttonComposite = new Group(composite, SWT.LEFT);
    GridLayout layout = new GridLayout();
    buttonComposite.setLayout(layout);
    GridData data = new GridData(GridData.HORIZONTAL_ALIGN_FILL
            | GridData.GRAB_HORIZONTAL);
    buttonComposite.setLayoutData(data);
    buttonComposite.setText("Prover"); 

    String label = "Remote Atelier B"; 
    remoteAtelierB = createRadioButton(buttonComposite, label);
    remoteAtelierB.addSelectionListener(new SelectionAdapter() {

        public void widgetSelected(SelectionEvent e) {
            selectAtelierB(remoteAtelierB.getSelection());
        }
    });
    remoteAtelierB.setSelection(useRemoteAtelier);
    
    label = "&URL for Jab RMI service:";
    
    Composite url = new Composite(buttonComposite, SWT.NULL);
    
    layout = new GridLayout();
    layout.numColumns = 2;
    url.setLayout(layout);
    
    urlL = new Label(url, SWT.NULL);
    urlL.setText(label);
    urlL.setEnabled(useRemoteAtelier);
   
    urlT = new Text(url, SWT.SINGLE | SWT.BORDER);
    urlT.setText(urlS);
	data = new GridData(GridData.FILL_HORIZONTAL);
//	data.horizontalSpan = 2;
	urlT.setLayoutData(data); 
    urlT.setEnabled(useRemoteAtelier);
    
    data = new GridData(GridData.FILL_HORIZONTAL);
    data.horizontalIndent = 20;
    url.setLayoutData(data);

    label = "Local AtelierB";
    localB4Free = createRadioButton(buttonComposite, label);
    localB4Free.addSelectionListener(new SelectionAdapter() {

        public void widgetSelected(SelectionEvent e) {
            selectAtelierB(remoteAtelierB.getSelection());
        }
    });
    localB4Free.setSelection(!useRemoteAtelier);

    Composite b4free = new Composite(buttonComposite, SWT.NULL);
    
    layout = new GridLayout();
    layout.numColumns = 3;
    b4free.setLayout(layout);
    
    bbatchL = new Label(b4free, SWT.NULL);
    bbatchL.setText("bbatch exe");
    bbatchL.setEnabled(!useRemoteAtelier);
   
    bbatchT = new Text(b4free, SWT.SINGLE | SWT.BORDER | SWT.READ_ONLY);
    bbatchT.setText(bbatchS);
	data = new GridData(GridData.FILL_HORIZONTAL);
//	data.horizontalSpan = 2;
	bbatchT.setLayoutData(data); 
	bbatchT.setEnabled(!useRemoteAtelier);
	
	bbatchB = new Button(b4free, SWT.PUSH);
	bbatchB.setText("Browse...");
	bbatchB.setEnabled(!useRemoteAtelier);
	bbatchB.addSelectionListener(new SelectionAdapter() {

        public void widgetSelected(SelectionEvent e) {
        	FileDialog dialog = new FileDialog(getShell());
        	String path = dialog.open();
			if (path != null) {
				bbatchT.setText(path);
			}
			}
        
    });
   
	   ressourceL = new Label(b4free, SWT.NULL);
	   ressourceL.setText("ressource file");
	   ressourceL.setEnabled(!useRemoteAtelier);
	   
	   ressourceT = new Text(b4free, SWT.SINGLE | SWT.BORDER);
	   ressourceT.setText(ressourceS);
		data = new GridData(GridData.FILL_HORIZONTAL);
//		data.horizontalSpan = 2;
		ressourceT.setLayoutData(data); 
		ressourceT.setEnabled(!useRemoteAtelier);

		ressourceB = new Button(b4free, SWT.PUSH);
		ressourceB.setText("Browse...");
		ressourceB.setEnabled(!useRemoteAtelier);
		ressourceB.addSelectionListener(new SelectionAdapter() {

	        public void widgetSelected(SelectionEvent e) {
	        	FileDialog dialog = new FileDialog(getShell());
	        	String path = dialog.open();
				if (path != null) {
					ressourceT.setText(path);
				}
				}
	        
	    });
		
		   bdpL = new Label(b4free, SWT.NULL);
		   bdpL.setText("bdp directory");
		   bdpL.setEnabled(!useRemoteAtelier);
		   
		   bdpT = new Text(b4free, SWT.SINGLE | SWT.BORDER);
		   bdpT.setText(bdpS);
			data = new GridData(GridData.FILL_HORIZONTAL);
//			data.horizontalSpan = 2;
			bdpT.setLayoutData(data); 
			bdpT.setEnabled(!useRemoteAtelier);

			bdpB = new Button(b4free, SWT.PUSH);
			bdpB.setText("Browse...");
			bdpB.setEnabled(!useRemoteAtelier);
			bdpB.addSelectionListener(new SelectionAdapter() {

		        public void widgetSelected(SelectionEvent e) {
		        	DirectoryDialog dialog = new DirectoryDialog(getShell());
		        	String path = dialog.open();
					if (path != null) {
						bdpT.setText(path);
					}
					}
		        
		    });
			
				Group versions = new Group(b4free, SWT.LEFT);
		versions.setText("Version");
	    layout = new GridLayout();
	    versions.setLayout(layout);
	    versions.setEnabled(!useRemoteAtelier);

	    versionB4Free20 = createRadioButton(versions, "B4Free 2.0");
	    versionB4Free20.setEnabled(!useRemoteAtelier);
	    versionB4Free20.setSelection(version == VersionB4free);
	    versionB4Free20.addSelectionListener(new SelectionAdapter() {

	        public void widgetSelected(SelectionEvent e) {
	            selectVersion(versionB4Free20.getSelection() ? VersionB4free : version);
	        }
	    });

	    Composite cB4F = new Composite(versions, SWT.NULL);
	    layout = new GridLayout();
	    layout.numColumns = 3;
	    cB4F.setLayout(layout);
	    
	    clickNProveL = new Label(cB4F, SWT.NULL);
	    clickNProveL.setText("Click'n'Prove Executable");
	    clickNProveL.setEnabled(!useRemoteAtelier && version == VersionB4free);
	    
	    clickNProveT = new Text(cB4F, SWT.SINGLE | SWT.BORDER);
	    clickNProveT.setText(clickNProveS);
	    data = new GridData(GridData.FILL_HORIZONTAL);
//	    data.horizontalSpan = 2;
	    clickNProveT.setLayoutData(data); 
	    clickNProveT.setEnabled(!useRemoteAtelier && version == VersionB4free);
	    
	    clickNProveB = new Button(cB4F, SWT.PUSH);
	    clickNProveB.setText("Browse...");
	    clickNProveB.setEnabled(!useRemoteAtelier && version == VersionB4free);
	    clickNProveB.addSelectionListener(new SelectionAdapter() {
	    	
	    	public void widgetSelected(SelectionEvent e) {
	    		FileDialog dialog = new FileDialog(getShell());
	    		String path = dialog.open();
	    		if (path != null) {
	    			clickNProveT.setText(path);
	    		}
	    	}
	    	
	    });
	    data = new GridData(GridData.FILL_HORIZONTAL);
	    data.horizontalIndent = 20;
	    cB4F.setLayoutData(data);

	    
	    version36 = createRadioButton(versions, "3.6");
	    version36.setEnabled(!useRemoteAtelier);
	    version36.setSelection(version == Version36);
	    version36.addSelectionListener(new SelectionAdapter() {

	        public void widgetSelected(SelectionEvent e) {
	            selectVersion(version36.getSelection() ? Version36 : version);
	        }
	    });
	    
	    version35 = createRadioButton(versions, "3.5");
	    version35.setEnabled(!useRemoteAtelier);
	    version35.setSelection(version == Version35);
	    version35.addSelectionListener(new SelectionAdapter() {
	    	
	    	public void widgetSelected(SelectionEvent e) {
	    		selectVersion(version35.getSelection() ? Version35 : version);
	    	}
	    });
	    
	    Composite c35 = new Composite(versions, SWT.NULL);
	    layout = new GridLayout();
	    layout.numColumns = 3;
	    c35.setLayout(layout);
	    
	    abDefL = new Label(c35, SWT.NULL);
	    abDefL.setText("ab_def file");
	    abDefL.setEnabled(!useRemoteAtelier && version == Version35);
	    
	    abDefT = new Text(c35, SWT.SINGLE | SWT.BORDER);
	    abDefT.setText(abDefS);
	    data = new GridData(GridData.FILL_HORIZONTAL);
//	    data.horizontalSpan = 2;
	    abDefT.setLayoutData(data); 
	    abDefT.setEnabled(!useRemoteAtelier && version == Version35);
	    
	    abDefB = new Button(c35, SWT.PUSH);
	    abDefB.setText("Browse...");
	    abDefB.setEnabled(!useRemoteAtelier && version == Version35);
	    abDefB.addSelectionListener(new SelectionAdapter() {
	    	
	    	public void widgetSelected(SelectionEvent e) {
	    		FileDialog dialog = new FileDialog(getShell());
	    		String path = dialog.open();
	    		if (path != null) {
	    			abDefT.setText(path);
	    		}
	    	}
	    	
	    });
	    data = new GridData(GridData.FILL_HORIZONTAL);
	    data.horizontalIndent = 20;
	    c35.setLayoutData(data);
	    
	    data = new GridData(GridData.FILL_HORIZONTAL);
	    data.horizontalSpan = 3;
	    versions.setLayoutData(data);
	    
	    
	    data = new GridData(GridData.FILL_HORIZONTAL);
	    data.horizontalIndent = 20;
    b4free.setLayoutData(data);
//    label = WorkbenchMessages
//            .getString("WorkbenchPreference.singleClick_SelectOnHover"); //$NON-NLS-1$				
//    selectOnHoverButton = new Button(buttonComposite, SWT.CHECK | SWT.LEFT);
//    selectOnHoverButton.setText(label);
//    selectOnHoverButton.setEnabled(!useRemoteAtelier);
//    selectOnHoverButton.setSelection(selectOnHover);
//    selectOnHoverButton.addSelectionListener(new SelectionAdapter() {
//
//        public void widgetSelected(SelectionEvent e) {
//            selectOnHover = selectOnHoverButton.getSelection();
//        }
//    });
//    data = new GridData();
//    data.horizontalIndent = 20;
//    selectOnHoverButton.setLayoutData(data);
//
//    label = WorkbenchMessages
//            .getString("WorkbenchPreference.singleClick_OpenAfterDelay"); //$NON-NLS-1$				
//    openAfterDelayButton = new Button(buttonComposite, SWT.CHECK | SWT.LEFT);
//    openAfterDelayButton.setText(label);
//    openAfterDelayButton.setEnabled(!useRemoteAtelier);
//    openAfterDelayButton.setSelection(openAfterDelay);
//    openAfterDelayButton.addSelectionListener(new SelectionAdapter() {
//
//        public void widgetSelected(SelectionEvent e) {
//            openAfterDelay = openAfterDelayButton.getSelection();
//        }
//    });
//    data = new GridData();
//    data.horizontalIndent = 20;
//    openAfterDelayButton.setLayoutData(data);
//
//    createNoteComposite(font, buttonComposite, WorkbenchMessages
//            .getString("Preference.note"), //$NON-NLS-1$
//            WorkbenchMessages
//                    .getString("WorkbenchPreference.noEffectOnAllViews")); //$NON-NLS-1$
//    
    applyDialogFont(composite);

    return composite;
}
    private Composite createComposite(Composite parent) {
        Composite composite = new Composite(parent, SWT.NONE);
        GridLayout layout = new GridLayout();
        layout.marginWidth = 0;
        layout.marginHeight = 0;
        composite.setLayout(layout);
        composite.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_FILL
                | GridData.HORIZONTAL_ALIGN_FILL));
        return composite;
    }
    
    protected static Button createRadioButton(Composite parent, String label) {
        Button button = new Button(parent, SWT.RADIO | SWT.LEFT);
        button.setText(label);
        return button;
    }
    
    private void selectAtelierB(boolean ab) {
    	useRemoteAtelier = ab;
    	urlL.setEnabled(useRemoteAtelier);
    	urlT.setEnabled(useRemoteAtelier);
    	bbatchL.setEnabled(!useRemoteAtelier);
    	bbatchT.setEnabled(!useRemoteAtelier);
    	bbatchB.setEnabled(!useRemoteAtelier);
    	ressourceL.setEnabled(!useRemoteAtelier);
    	ressourceT.setEnabled(!useRemoteAtelier);
    	ressourceB.setEnabled(!useRemoteAtelier);
    	bdpL.setEnabled(!useRemoteAtelier);
    	bdpT.setEnabled(!useRemoteAtelier);
    	bdpB.setEnabled(!useRemoteAtelier);
    	version36.setEnabled(!useRemoteAtelier);
    	version35.setEnabled(!useRemoteAtelier);
    	abDefL.setEnabled(!useRemoteAtelier && version == Version35);
    	abDefT.setEnabled(!useRemoteAtelier && version == Version35);
    	abDefB.setEnabled(!useRemoteAtelier && version == Version35);
    	clickNProveL.setEnabled(!useRemoteAtelier && version == VersionB4free);
      	clickNProveT.setEnabled(!useRemoteAtelier && version == VersionB4free);
      	clickNProveB.setEnabled(!useRemoteAtelier && version == VersionB4free);
          }

    private void selectVersion(int v) {
    	this.version = v;
    	abDefL.setEnabled(!useRemoteAtelier && version == Version35);
       	abDefT.setEnabled(!useRemoteAtelier && version == Version35);
       	abDefB.setEnabled(!useRemoteAtelier && version == Version35);
           }
    
///**
//	 * Creates the field editors. Field editors are abstractions of
//	 * the common GUI blocks needed to manipulate various types
//	 * of preferences. Each field editor knows how to save and
//	 * restore itself.
//	 */
//	public void createFieldEditors() {
//		addField(
//			new StringFieldEditor(
//				BPlugin.JAB_RMI_URL,
//				"&URL for Jab RMI service:",
//				getFieldEditorParent()));
//		addField(new RadioGroupFieldEditor(
//								  			"GeneralPage.DoubleClick", "Prover", 1,
//								  			new String[][] {
//								  				{"Remote Atelier B", "atelierB"},
//								  				{"Local B4Free", "b4free"}
//								  			},
//								  			getFieldEditorParent(),
//								            true));
//
//	}

//	public void init(IWorkbench workbench) {
//	}
	   /**
     * Returns preference store that belongs to the our plugin.
     * 
     * @return the preference store for this plugin
     */
    protected IPreferenceStore doGetPreferenceStore() {
        return BPlugin.getDefault().getPreferenceStore();
    }

    /**
     * @see IWorkbenchPreferencePage
     */
    public void init(IWorkbench aWorkbench) {
        IPreferenceStore store = getPreferenceStore();
        useRemoteAtelier = store
                .getBoolean(BPlugin.USE_REMOTE_ATELIER);
        urlS = store.getString(BPlugin.JAB_RMI_URL);
        bbatchS = store
                .getString(BPlugin.B4FREE_BBATCH);
        ressourceS = store.getString(BPlugin.B4FREE_RESSOURCE);
        bdpS = store.getString(BPlugin.BDP);
        version = store.getInt(BPlugin.AB_VERSION);
        abDefS =  store.getString(BPlugin.AB_DEF);
        clickNProveS =  store.getString(BPlugin.CLICK_N_PROVE_EXE);
    }

  /*  *//**
     * The default button has been pressed.
     *//*
    protected void performDefaults() {
        IPreferenceStore store = getPreferenceStore();
        stickyCycleButton.setSelection(store
                .getBoolean(IPreferenceConstants.STICKY_CYCLE));
        openOnSingleClick = store
                .getDefaultBoolean(IPreferenceConstants.OPEN_ON_SINGLE_CLICK);
        selectOnHover = store
                .getDefaultBoolean(IPreferenceConstants.SELECT_ON_HOVER);
        openAfterDelay = store
                .getDefaultBoolean(IPreferenceConstants.OPEN_AFTER_DELAY);
        singleClickButton.setSelection(openOnSingleClick);
        doubleClickButton.setSelection(!openOnSingleClick);
        selectOnHoverButton.setSelection(selectOnHover);
        openAfterDelayButton.setSelection(openAfterDelay);
        selectOnHoverButton.setEnabled(openOnSingleClick);
        openAfterDelayButton.setEnabled(openOnSingleClick);
        stickyCycleButton.setSelection(store
                .getDefaultBoolean(IPreferenceConstants.STICKY_CYCLE));

        super.performDefaults();
    }
*/
    /**
     * The user has pressed Ok. Store/apply this page's values appropriately.
     */
    public boolean performOk() {
        IPreferenceStore store = getPreferenceStore();

        // store the keep cycle part dialogs sticky preference
        store.setValue(BPlugin.USE_REMOTE_ATELIER, 
                remoteAtelierB.getSelection());
        store.setValue(BPlugin.JAB_RMI_URL,
                urlT.getText());
        store.setValue(BPlugin.B4FREE_BBATCH, bbatchT.getText());
        store.setValue(BPlugin.B4FREE_RESSOURCE,ressourceT.getText());
        store.setValue(BPlugin.BDP, bdpT.getText());
        store.setValue(BPlugin.AB_VERSION, version);
        store.setValue(BPlugin.AB_DEF, abDefT.getText());
        store.setValue(BPlugin.CLICK_N_PROVE_EXE, clickNProveT.getText());
         
  /*      int singleClickMethod = openOnSingleClick ? OpenStrategy.SINGLE_CLICK
                : OpenStrategy.DOUBLE_CLICK;
        if (openOnSingleClick) {
            if (selectOnHover) {
                singleClickMethod |= OpenStrategy.SELECT_ON_HOVER;
            }
            if (openAfterDelay) {
                singleClickMethod |= OpenStrategy.ARROW_KEYS_OPEN;
            }
        }
        OpenStrategy.setOpenMethod(singleClickMethod);
*/
        BPlugin.getDefault().savePluginPreferences();
        return true;
    }
}
