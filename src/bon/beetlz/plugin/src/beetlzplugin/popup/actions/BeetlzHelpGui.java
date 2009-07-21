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
public class BeetlzHelpGui extends org.eclipse.swt.widgets.Dialog {

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
  private Button buttonOK;
  private Label label8;
  private Label label7;
  private Button buttonSourceBon;
  private Button buttonPureBon;
  private Button buttonPrintWarning;
  private Button buttonHelp;
  private Label label1;
  private Label label6;
  private Label label5;
  private Label label4;
  private Label label3;
  private Label label2;
  private Label labelWarningHelp;
  private Label labelJmlHelp;
  private Button buttonUseBasics;
  private Button buttonVerbose;




  public BeetlzHelpGui(Shell parent, int style) {
    super(parent, style);

  }

  public void open() {
    try {
      Shell parent = getParent();
      dialogShell = new Shell(parent, SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
      
      Listener listener = new Listener() {
           public void handleEvent(Event event) {
                
                
                if (event.widget == buttonOK) {
                  dialogShell.dispose();
                }
           } 
        };
      dialogShell.setLayout(new FormLayout());
      {
        buttonOK = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonOK.setText("OK");//$NON-NLS-1$
        buttonOK.addListener(SWT.Selection, listener);
        FormData buttonOKLData = new FormData();
        buttonOKLData.width = 115;
        buttonOKLData.height = 28;
        buttonOKLData.left =  new FormAttachment(0, 1000, 581);
        buttonOKLData.top =  new FormAttachment(0, 1000, 390);
        buttonOK.setLayoutData(buttonOKLData);
      }
      {
        labelWarningHelp = new Label(dialogShell, SWT.NONE);
        labelWarningHelp.setText(Messages.getString("BeetlzHelpGui.warningHelp")); //$NON-NLS-1$
        FormData labelWarningHelpLData = new FormData();
        labelWarningHelpLData.width = 270;
        labelWarningHelpLData.height = 36;
        labelWarningHelpLData.left =  new FormAttachment(0, 1000, 278);
        labelWarningHelpLData.top =  new FormAttachment(0, 1000, 52);
        labelWarningHelp.setLayoutData(labelWarningHelpLData);
        labelWarningHelp.setFont(SWTResourceManager.getFont("Palatino Linotype", 9, 3, false, false)); //$NON-NLS-1$
      }
      {
        labelJmlHelp = new Label(dialogShell, SWT.NONE);
        labelJmlHelp.setText(Messages.getString("BeetlzHelpGui.jmlHelp")); //$NON-NLS-1$
        FormData labelJmlHelpLData = new FormData();
        labelJmlHelpLData.width = 253;
        labelJmlHelpLData.height = 37;
        labelJmlHelpLData.left =  new FormAttachment(0, 1000, 19);
        labelJmlHelpLData.top =  new FormAttachment(0, 1000, 46);
        labelJmlHelp.setLayoutData(labelJmlHelpLData);
        labelJmlHelp.setFont(SWTResourceManager.getFont("Palatino Linotype", 9, 3, false, false)); //$NON-NLS-1$

      }
      {
        buttonHelp = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonHelp.setText(Messages.getString("BeetlzGui.help"));//$NON-NLS-1$
        buttonHelp.addListener(SWT.Selection, listener);
        FormData buttonHelpLData = new FormData();
        buttonHelpLData.width = 134;
        buttonHelpLData.height = 42;
        buttonHelpLData.left =  new FormAttachment(0, 1000, 581);
        buttonHelpLData.top =  new FormAttachment(0, 1000, 253);
        buttonHelp.setLayoutData(buttonHelpLData);
        buttonHelp.setEnabled(false);
      }
      {
        buttonUseBasics = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseBasics.setText(Messages.getString("BeetlzGui.useBasicSettings"));//$NON-NLS-1$
        FormData buttonUseBasicsLData = new FormData();
        buttonUseBasicsLData.width = 111;
        buttonUseBasicsLData.height = 15;
        buttonUseBasicsLData.left =  new FormAttachment(0, 1000, 280);
        buttonUseBasicsLData.top =  new FormAttachment(0, 1000, 253);
        buttonUseBasics.setLayoutData(buttonUseBasicsLData);
        buttonUseBasics.setEnabled(false);
      }
      {
        buttonNullCheck = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonNullCheck.setText(Messages.getString("BeetlzGui.checkNullity"));//$NON-NLS-1$
        FormData buttonNullCheckLData = new FormData();
        buttonNullCheckLData.width = 158;
        buttonNullCheckLData.height = 17;
        buttonNullCheckLData.left =  new FormAttachment(0, 1000, 19);
        buttonNullCheckLData.top =  new FormAttachment(0, 1000, 171);
        buttonNullCheck.setLayoutData(buttonNullCheckLData);
        buttonNullCheck.setEnabled(false);
      }
      {
        buttonUseJava = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseJava.setText(Messages.getString("BeetlzGui.showJava"));//$NON-NLS-1$
        FormData buttonUseJavaLData = new FormData();
        buttonUseJavaLData.width = 105;
        buttonUseJavaLData.height = 17;
        buttonUseJavaLData.left =  new FormAttachment(0, 1000, 19);
        buttonUseJavaLData.top =  new FormAttachment(0, 1000, 94);
        buttonUseJava.setLayoutData(buttonUseJavaLData);
        buttonUseJava.setEnabled(false);
      }
      {
        buttonCancel = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonCancel.setText(Messages.getString("BeetlzGui.cancel"));//$NON-NLS-1$
        buttonCancel.addListener(SWT.Selection, listener);
        FormData buttonCancelLData = new FormData();
        buttonCancelLData.width = 134;
        buttonCancelLData.height = 43;
        buttonCancelLData.left =  new FormAttachment(0, 1000, 581);
        buttonCancelLData.top =  new FormAttachment(0, 1000, 307);
        buttonCancel.setLayoutData(buttonCancelLData);
        buttonCancel.setEnabled(false);
      }
      {
        buttonGo = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonGo.setText(Messages.getString("BeetlzGui.go"));//$NON-NLS-1$
        buttonGo.setData(new Integer(13));
        buttonGo.addListener(SWT.Selection, listener);
            //cancelButton.addListener(SWT.Selection, listener);
        
        
        FormData buttonGoLData = new FormData();
        buttonGoLData.width = 127;
        buttonGoLData.height = 41;
        buttonGoLData.left =  new FormAttachment(0, 1000, 581);
        buttonGoLData.top =  new FormAttachment(0, 1000, 44);
        buttonGo.setLayoutData(buttonGoLData);
        buttonGo.setEnabled(false);
        buttonGo.setFocus();
      }
      {
        groupSource = new Group(dialogShell, SWT.NONE);
        GridLayout groupSourceLayout = new GridLayout();
        groupSourceLayout.makeColumnsEqualWidth = true;
        groupSource.setLayout(groupSourceLayout);
        groupSource.setText(Messages.getString("BeetlzGui.sourceIs"));//$NON-NLS-1$
        FormData groupSourceLData = new FormData();
        groupSourceLData.width = 146;
        groupSourceLData.height = 71;
        groupSourceLData.left =  new FormAttachment(0, 1000, 19);
        groupSourceLData.top =  new FormAttachment(0, 1000, 326);
        groupSource.setLayoutData(groupSourceLData);
        groupSource.setEnabled(false);
        {
          final Button buttonSourceDefault = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceDefault.setText(Messages.getString("BeetlzGui.default"));//$NON-NLS-1$
          GridData buttonSourceDefaultLData = new GridData();
          buttonSourceDefault.setLayoutData(buttonSourceDefaultLData);
        }
        {
          buttonSourceBon = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceBon.setText(Messages.getString("BeetlzGui.bonIsSource"));//$NON-NLS-1$
          GridData buttonSourceBonLData = new GridData();
          buttonSourceBon.setLayoutData(buttonSourceBonLData);
        }
        {
          buttonSourceJava = new Button(groupSource, SWT.RADIO | SWT.LEFT);
          buttonSourceJava.setText(Messages.getString("BeetlzGui.javaIsSource"));//$NON-NLS-1$
          GridData buttonSourceJavaLData = new GridData();
          buttonSourceJava.setLayoutData(buttonSourceJavaLData);
        }
      }
      {
        buttonPureBon = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPureBon.setText(Messages.getString("BeetlzGui.usePureBon"));//$NON-NLS-1$
        FormData buttonPureBonLData = new FormData();
        buttonPureBonLData.width = 176;
        buttonPureBonLData.height = 17;
        buttonPureBonLData.left =  new FormAttachment(0, 1000, 19);
        buttonPureBonLData.top =  new FormAttachment(0, 1000, 251);
        buttonPureBon.setLayoutData(buttonPureBonLData);
        buttonPureBon.setEnabled(false);
      }
      {
        buttonPrintErrors = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPrintErrors.setText(Messages.getString("BeetlzGui.printErrors"));//$NON-NLS-1$
        FormData buttonNoErrorsLData = new FormData();
        buttonNoErrorsLData.width = 112;
        buttonNoErrorsLData.height = 21;
        buttonNoErrorsLData.left =  new FormAttachment(0, 1000, 278);
        buttonNoErrorsLData.top =  new FormAttachment(0, 1000, 94);
        buttonPrintErrors.setLayoutData(buttonNoErrorsLData);
        buttonPrintErrors.setEnabled(false);
      }
      {
        buttonPrintWarning = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonPrintWarning.setText(Messages.getString("BeetlzGui.printWarnings"));//$NON-NLS-1$
        FormData buttonNoWarningLData = new FormData();
        buttonNoWarningLData.width = 125;
        buttonNoWarningLData.height = 21;
        buttonNoWarningLData.left =  new FormAttachment(0, 1000, 278);
        buttonNoWarningLData.top =  new FormAttachment(0, 1000, 33);
        buttonPrintWarning.setLayoutData(buttonNoWarningLData);
        buttonPrintWarning.setEnabled(false);
      }
      {
        buttonUseJml = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseJml.setText(Messages.getString("BeetlzGui.useJml"));//$NON-NLS-1$
        FormData buttonNoJmlLData = new FormData();
        buttonNoJmlLData.width = 152;
        buttonNoJmlLData.height = 14;
        buttonNoJmlLData.left =  new FormAttachment(0, 1000, 19);
        buttonNoJmlLData.top =  new FormAttachment(0, 1000, 33);
        buttonUseJml.setLayoutData(buttonNoJmlLData);
        buttonUseJml.setEnabled(false);
      }
      {
        buttonVerbose = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonVerbose.setText(Messages.getString("BeetlzGui.verbose"));//$NON-NLS-1$
        FormData buttonDebugLData = new FormData();
        buttonDebugLData.width = 113;
        buttonDebugLData.height = 15;
        buttonDebugLData.left =  new FormAttachment(0, 1000, 280);
        buttonDebugLData.top =  new FormAttachment(0, 1000, 171);
        buttonVerbose.setLayoutData(buttonDebugLData);
        buttonVerbose.setEnabled(false);
      }
      {
        labelWelcomeMssg = new Label(dialogShell, SWT.NONE);
        labelWelcomeMssg.setText(Messages.getString("BeetlzGui.selectYourOptions"));//$NON-NLS-1$
        FormData labelWelcomeMssgLData = new FormData();
        labelWelcomeMssgLData.width = 247;
        labelWelcomeMssgLData.height = 20;
        labelWelcomeMssgLData.left =  new FormAttachment(0, 1000, 19);
        labelWelcomeMssgLData.top =  new FormAttachment(0, 1000, 10);
        labelWelcomeMssg.setLayoutData(labelWelcomeMssgLData);
        labelWelcomeMssg.setEnabled(false);
      }
      {
        label1 = new Label(dialogShell, SWT.NONE);
        label1.setText(Messages.getString("BeetlzHelpGui.errorHelp")); //$NON-NLS-1$
        FormData label1LData = new FormData();
        label1LData.left =  new FormAttachment(0, 1000, 278);
        label1LData.top =  new FormAttachment(0, 1000, 115);
        label1LData.width = 291;
        label1LData.height = 34;
        label1.setLayoutData(label1LData);
        label1.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label2 = new Label(dialogShell, SWT.NONE);
        label2.setText(Messages.getString("BeetlzHelpGui.javaHelp")); //$NON-NLS-1$
        FormData label2LData = new FormData();
        label2LData.left =  new FormAttachment(0, 1000, 19);
        label2LData.top =  new FormAttachment(0, 1000, 110);
        label2LData.width = 253;
        label2LData.height = 36;
        label2.setLayoutData(label2LData);
        label2.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label3 = new Label(dialogShell, SWT.NONE);
        label3.setText(Messages.getString("BeetlzHelpGui.nullityHelp")); //$NON-NLS-1$
        FormData label3LData = new FormData();
        label3LData.left =  new FormAttachment(0, 1000, 19);
        label3LData.top =  new FormAttachment(0, 1000, 188);
        label3LData.width = 249;
        label3LData.height = 33;
        label3.setLayoutData(label3LData);
        label3.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label4 = new Label(dialogShell, SWT.NONE);
        label4.setText(Messages.getString("BeetlzHelpGui.debugHelp")); //$NON-NLS-1$
        FormData label4LData = new FormData();
        label4LData.left =  new FormAttachment(0, 1000, 280);
        label4LData.top =  new FormAttachment(0, 1000, 188);
        label4LData.width = 268;
        label4LData.height = 33;
        label4.setLayoutData(label4LData);
        label4.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label5 = new Label(dialogShell, SWT.NONE);
        label5.setText(Messages.getString("BeetlzHelpGui.pureBonHelp")); //$NON-NLS-1$
        FormData label5LData = new FormData();
        label5LData.left =  new FormAttachment(0, 1000, 19);
        label5LData.top =  new FormAttachment(0, 1000, 267);
        label5LData.width = 242;
        label5LData.height = 35;
        label5.setLayoutData(label5LData);
        label5.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label6 = new Label(dialogShell, SWT.NONE);
        label6.setText(Messages.getString("BeetlzHelpGui.basicsHelp")); //$NON-NLS-1$
        FormData label6LData = new FormData();
        label6LData.left =  new FormAttachment(0, 1000, 280);
        label6LData.top =  new FormAttachment(0, 1000, 267);
        label6LData.width = 283;
        label6LData.height = 67;
        label6.setLayoutData(label6LData);
        label6.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label7 = new Label(dialogShell, SWT.NONE);
        label7.setText(Messages.getString("BeetlzHelpGui.startConsistencyCheck")); //$NON-NLS-1$
        FormData label7LData = new FormData();
        label7LData.left =  new FormAttachment(0, 1000, 581);
        label7LData.top =  new FormAttachment(0, 1000, 94);
        label7LData.width = 134;
        label7LData.height = 37;
        label7.setLayoutData(label7LData);
        label7.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      {
        label8 = new Label(dialogShell, SWT.NONE);
        label8.setText(Messages.getString("BeetlzHelpGui.18")); //$NON-NLS-1$
        FormData label8LData = new FormData();
        label8LData.left =  new FormAttachment(0, 1000, 177);
        label8LData.top =  new FormAttachment(0, 1000, 349);
        label8LData.width = 265;
        label8LData.height = 60;
        label8.setLayoutData(label8LData);
        label8.setFont(SWTResourceManager.getFont("Palatino Linotype",9,3,false,false)); //$NON-NLS-1$
      }
      dialogShell.layout();
      dialogShell.pack();      
      dialogShell.setSize(785, 466);
      dialogShell.setText("Beetlz Eclipse Plugin"); //$NON-NLS-1$
      dialogShell.setToolTipText(Messages.getString("BeetlzHelpGui.startConsistencyCheck")); //$NON-NLS-1$
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
  
  
    
  
  

}
