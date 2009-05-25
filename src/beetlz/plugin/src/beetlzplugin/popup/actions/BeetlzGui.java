package beetlzplugin.popup.actions;

import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.SWT;


/**
* This code was edited or generated using CloudGarden's Jigloo
* SWT/Swing GUI Builder, which is free for non-commercial
* use. If Jigloo is being used commercially (ie, by a corporation,
* company or business for any purpose whatever) then you
* should purchase a license for each developer using Jigloo.
* Please visit www.cloudgarden.com for details.
* Use of Jigloo implies acceptance of these licensing terms.
* A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR
* THIS MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED
* LEGALLY FOR ANY CORPORATE OR COMMERCIAL PURPOSE.
*/
public class BeetlzGui extends org.eclipse.swt.widgets.Dialog {

  private Shell dialogShell;
  private Label labelWelcomeMssg;
  private Button buttonUseJml;
  private Button buttonNullCheck;
  private Button buttonUseJava;
  private Button buttonCancel;
  private Button buttonGo;
  private Button buttonPrintErrors;
  private Button buttonSourceJava;
  private Group groupSource;
  private Button buttonSourceBon;
  private Button buttonPureBon;
  private Button buttonPrintWarning;
  private Button buttonHelp;
  private Button buttonUseBasics;
  private Button buttonVerbose;

  private BeetlzCheck action;


  public BeetlzGui(Shell parent, int style, BeetlzCheck a) {
    super(parent, style);
    action = a;
  }

  public void open() {
    try {
      Shell parent = getParent();
      dialogShell = new Shell(parent, SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);

      {
        //Register as a resource user - SWTResourceManager will
        //handle the obtaining and disposing of resources
        //SWTResourceManager.registerResourceUser(dialogShell);
      }
      
      Listener listener = new Listener() {
           public void handleEvent(Event event) {
                if (event.widget == buttonGo) {
                  //get our selected options:
                  action.useJml = buttonUseJml.getSelection();
                  action.useJava = buttonUseJava.getSelection();
                  action.printError = buttonPrintErrors.getSelection();
                  action.printWarning = buttonPrintWarning.getSelection();
                  action.verbose = buttonVerbose.getSelection();
                  action.pureBon = buttonPureBon.getSelection();
                  action.useBasics = buttonUseBasics.getSelection();
                  action.nullCheck = buttonNullCheck.getSelection();
                  if (buttonSourceJava.getSelection()) action.source = "java"; //$NON-NLS-1$
                  else if(buttonSourceBon.getSelection()) action.source = "bon"; //$NON-NLS-1$
                  else action.source = "default"; //$NON-NLS-1$
                  
                  dialogShell.dispose();
                }
                
                if (event.widget == buttonCancel) {
                  action.cancel = true;
                  dialogShell.dispose();
                }
                if (event.widget == buttonHelp) {
                  action.help = true;
                  dialogShell.dispose();
                }
                
           } 
        };
      dialogShell.setLayout(new FormLayout());
      {
        buttonHelp = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonHelp.setText(Messages.getString("BeetlzGui.help")); //$NON-NLS-1$
        buttonHelp.addListener(SWT.Selection, listener);
        FormData buttonHelpLData = new FormData();
        buttonHelpLData.width = 126;
        buttonHelpLData.height = 37;
        buttonHelpLData.left =  new FormAttachment(0, 1000, 326);
        buttonHelpLData.top =  new FormAttachment(0, 1000, 171);
        buttonHelp.setLayoutData(buttonHelpLData);
      }
      {
        buttonUseBasics = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseBasics.setText(Messages.getString("BeetlzGui.useBasicSettings")); //$NON-NLS-1$
        FormData buttonUseBasicsLData = new FormData();
        buttonUseBasicsLData.width = 158;
        buttonUseBasicsLData.height = 18;
        buttonUseBasicsLData.left =  new FormAttachment(0, 1000, 152);
        buttonUseBasicsLData.top =  new FormAttachment(0, 1000, 138);
        buttonUseBasics.setLayoutData(buttonUseBasicsLData);
        buttonUseBasics.setSelection(action.useBasics);
      }
      {
        buttonNullCheck = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonNullCheck.setText(Messages.getString("BeetlzGui.checkNullity")); //$NON-NLS-1$
        FormData buttonNullCheckLData = new FormData();
        buttonNullCheckLData.width = 91;
        buttonNullCheckLData.height = 16;
        buttonNullCheckLData.left =  new FormAttachment(0, 1000, 19);
        buttonNullCheckLData.top =  new FormAttachment(0, 1000, 110);
        buttonNullCheck.setLayoutData(buttonNullCheckLData);
        buttonNullCheck.setSelection(action.nullCheck);
      }
      {
        buttonUseJava = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseJava.setText(Messages.getString("BeetlzGui.showJava")); //$NON-NLS-1$
        FormData buttonUseJavaLData = new FormData();
        buttonUseJavaLData.width = 115;
        buttonUseJavaLData.height = 19;
        buttonUseJavaLData.left =  new FormAttachment(0, 1000, 19);
        buttonUseJavaLData.top =  new FormAttachment(0, 1000, 64);
        buttonUseJava.setLayoutData(buttonUseJavaLData);
        buttonUseJava.setSelection(action.useJava);
      }
      {
        buttonCancel = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonCancel.setText(Messages.getString("BeetlzGui.cancel")); //$NON-NLS-1$
        buttonCancel.addListener(SWT.Selection, listener);
        FormData buttonCancelLData = new FormData();
        buttonCancelLData.width = 128;
        buttonCancelLData.height = 39;
        buttonCancelLData.left =  new FormAttachment(0, 1000, 326);
        buttonCancelLData.top =  new FormAttachment(0, 1000, 228);
        buttonCancel.setLayoutData(buttonCancelLData);
      }
      {
        buttonGo = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonGo.setText(Messages.getString("BeetlzGui.go")); //$NON-NLS-1$
        buttonGo.setData(new Integer(13));
        buttonGo.addListener(SWT.Selection, listener);
            //cancelButton.addListener(SWT.Selection, listener);
        
        
        FormData buttonGoLData = new FormData();
        buttonGoLData.width = 127;
        buttonGoLData.height = 39;
        buttonGoLData.left =  new FormAttachment(0, 1000, 326);
        buttonGoLData.top =  new FormAttachment(0, 1000, 42);
        buttonGo.setLayoutData(buttonGoLData);
        buttonGo.setFocus();
      }
      {
        groupSource = new Group(dialogShell, SWT.NONE);
        GridLayout groupSourceLayout = new GridLayout();
        groupSourceLayout.makeColumnsEqualWidth = true;
        groupSource.setLayout(groupSourceLayout);
        groupSource.setText(Messages.getString("BeetlzGui.sourceIs")); //$NON-NLS-1$
        FormData groupSourceLData = new FormData();
        groupSourceLData.width = 144;
        groupSourceLData.height = 77;
        groupSourceLData.left =  new FormAttachment(0, 1000, 19);
        groupSourceLData.top =  new FormAttachment(0, 1000, 171);
        groupSource.setLayoutData(groupSourceLData);
        {
          final Button buttonSourceDefault = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceDefault.setText(Messages.getString("BeetlzGui.default")); //$NON-NLS-1$
          GridData buttonSourceDefaultLData = new GridData();
          buttonSourceDefault.setLayoutData(buttonSourceDefaultLData);
          if(action.source.equals("default")) buttonSourceDefault.setSelection(true); //$NON-NLS-1$
        }
        {
          buttonSourceBon = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceBon.setText(Messages.getString("BeetlzGui.bonIsSource")); //$NON-NLS-1$
          GridData buttonSourceBonLData = new GridData();
          buttonSourceBon.setLayoutData(buttonSourceBonLData);
          if(action.source.equals("bon")) buttonSourceBon.setSelection(true); //$NON-NLS-1$
        }
        {
          buttonSourceJava = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceJava.setText(Messages.getString("BeetlzGui.javaIsSource")); //$NON-NLS-1$
          GridData buttonSourceJavaLData = new GridData();
          buttonSourceJava.setLayoutData(buttonSourceJavaLData);
          if(action.source.equals("java")) buttonSourceJava.setSelection(true); //$NON-NLS-1$
        }
      }
      {
        buttonPureBon = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPureBon.setText(Messages.getString("BeetlzGui.usePureBon")); //$NON-NLS-1$
        FormData buttonPureBonLData = new FormData();
        buttonPureBonLData.width = 127;
        buttonPureBonLData.height = 18;
        buttonPureBonLData.left =  new FormAttachment(0, 1000, 19);
        buttonPureBonLData.top =  new FormAttachment(0, 1000, 138);
        buttonPureBon.setLayoutData(buttonPureBonLData);
        buttonPureBon.setSelection(action.pureBon);
      }
      {
        buttonPrintErrors = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPrintErrors.setText(Messages.getString("BeetlzGui.printErrors")); //$NON-NLS-1$
        FormData buttonNoErrorsLData = new FormData();
        buttonNoErrorsLData.width = 109;
        buttonNoErrorsLData.height = 19;
        buttonNoErrorsLData.left =  new FormAttachment(0, 1000, 152);
        buttonNoErrorsLData.top =  new FormAttachment(0, 1000, 64);
        buttonPrintErrors.setLayoutData(buttonNoErrorsLData);
        buttonPrintErrors.setSelection(action.printError);
      }
      {
        buttonPrintWarning = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPrintWarning.setText(Messages.getString("BeetlzGui.printWarnings")); //$NON-NLS-1$
        FormData buttonNoWarningLData = new FormData();
        buttonNoWarningLData.width = 125;
        buttonNoWarningLData.height = 17;
        buttonNoWarningLData.left =  new FormAttachment(0, 1000, 152);
        buttonNoWarningLData.top =  new FormAttachment(0, 1000, 42);
        buttonPrintWarning.setLayoutData(buttonNoWarningLData);
        buttonPrintWarning.setSelection(action.printWarning);
      }
      {
        buttonUseJml = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseJml.setText(Messages.getString("BeetlzGui.useJml")); //$NON-NLS-1$
        FormData buttonNoJmlLData = new FormData();
        buttonNoJmlLData.width = 121;
        buttonNoJmlLData.height = 16;
        buttonNoJmlLData.left =  new FormAttachment(0, 1000, 19);
        buttonNoJmlLData.top =  new FormAttachment(0, 1000, 42);
        buttonUseJml.setLayoutData(buttonNoJmlLData);
        buttonUseJml.setSelection(action.useJml);
      }
      {
        buttonVerbose = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonVerbose.setText(Messages.getString("BeetlzGui.verbose")); //$NON-NLS-1$
        FormData buttonDebugLData = new FormData();
        buttonDebugLData.width = 117;
        buttonDebugLData.height = 19;
        buttonDebugLData.left =  new FormAttachment(0, 1000, 152);
        buttonDebugLData.top =  new FormAttachment(0, 1000, 110);
        buttonVerbose.setLayoutData(buttonDebugLData);
        buttonVerbose.setSelection(action.verbose);
      }
      {
        labelWelcomeMssg = new Label(dialogShell, SWT.NONE);
        labelWelcomeMssg.setText(Messages.getString("BeetlzGui.selectYourOptions")); //$NON-NLS-1$
        FormData labelWelcomeMssgLData = new FormData();
        labelWelcomeMssgLData.width = 247;
        labelWelcomeMssgLData.height = 20;
        labelWelcomeMssgLData.left =  new FormAttachment(0, 1000, 19);
        labelWelcomeMssgLData.top =  new FormAttachment(0, 1000, 10);
        labelWelcomeMssg.setLayoutData(labelWelcomeMssgLData);
      }
      dialogShell.layout();
      dialogShell.pack();      
      dialogShell.setText("Beetlz Eclipse Plugin"); //$NON-NLS-1$
      dialogShell.setLocation(getParent().toDisplay(100, 100));
      dialogShell.open();
      Display display = dialogShell.getDisplay();
      while (!dialogShell.isDisposed()) {
        if (!display.readAndDispatch())
          display.sleep();
      }
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  
  
    
  
  public Label getLabelWelcomeMssg() {
    return labelWelcomeMssg;
  }
  
  public Button getButtonDebug() {
    return buttonVerbose;
  }
  
  public Button getButtonNoJml() {
    return buttonUseJml;
  }
  
  public Button getButtonNoErrors() {
    return buttonPrintErrors;
  }
  
  public Button getButtonPureBon() {
    return buttonPureBon;
  }
  
  public Button getButtonSourceBon() {
    return buttonSourceBon;
  }
  
  public Group getGroupSource() {
    return groupSource;
  }
  
  public Button getButtonSourceJava() {
    return buttonSourceJava;
  }
  
  
  public Button getButtonGo() {
    return buttonGo;
  }

}
