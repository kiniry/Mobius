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
public class BeetlzSkeletonGui extends org.eclipse.swt.widgets.Dialog {

  private Shell dialogShell;
  private Label labelWelcomeMssg;
  private Button buttonUseJml;
  private Button buttonNullCheck;
  private Button buttonCancel;
  private Button buttonGo;
  private Button buttonSourceJava;
  private Group groupSource;
  private Button buttonAllFiles;
  private Button buttonOneFile;
  private Button buttonConsole;
  private Group groupSkeletonOutput;
  private Button buttonSourceBon;
  private Button buttonPureBon;
  private Button buttonUseBasics;

  private BeetlzSkeleton action;


  public BeetlzSkeletonGui(Shell parent, int style, BeetlzSkeleton a) {
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
                  action.pureBon = buttonPureBon.getSelection();
                  action.useBasics = buttonUseBasics.getSelection();
                  action.nullCheck = buttonNullCheck.getSelection();
                  
                  if (buttonSourceJava.getSelection()) action.source = "java"; //$NON-NLS-1$
                  else if(buttonSourceBon.getSelection()) action.source = "bon"; //$NON-NLS-1$
                  else action.source = "default"; //$NON-NLS-1$
                  
                  if (buttonOneFile.getSelection()) action.output = "onefile"; //$NON-NLS-1$
                  else if (buttonAllFiles.getSelection()) action.output = "allfiles"; //$NON-NLS-1$
                  else {
                    action.output = "console"; //$NON-NLS-1$
                  }
                  dialogShell.dispose();
                }
                
                if (event.widget == buttonCancel) {
                  action.cancel = true;
                  dialogShell.dispose();
                }
           } 
        };
      dialogShell.setLayout(new FormLayout());
      {
        groupSkeletonOutput = new Group(dialogShell, SWT.NONE);
        GridLayout groupSkeletonOutputLayout = new GridLayout();
        groupSkeletonOutputLayout.makeColumnsEqualWidth = true;
        groupSkeletonOutput.setLayout(groupSkeletonOutputLayout);
        groupSkeletonOutput.setText(Messages.getString("BeetlzSkeletonGui.chooseOutput")); //$NON-NLS-1$
        FormData groupSkeletonOutputLData = new FormData();
        groupSkeletonOutputLData.width = 148;
        groupSkeletonOutputLData.height = 90;
        groupSkeletonOutputLData.left =  new FormAttachment(0, 1000, 15);
        groupSkeletonOutputLData.top =  new FormAttachment(0, 1000, 130);
        groupSkeletonOutput.setLayoutData(groupSkeletonOutputLData);
        {
          buttonConsole = new Button(groupSkeletonOutput, SWT.RADIO | SWT.LEFT);
          buttonConsole.setText(Messages.getString("BeetlzSkeletonGui.printConsole")); //$NON-NLS-1$
          GridData buttonConsoleLData = new GridData();
          buttonConsole.setLayoutData(buttonConsoleLData);
          buttonConsole.setSelection(true);
        }
        {
          buttonOneFile = new Button(groupSkeletonOutput, SWT.RADIO | SWT.LEFT);
          buttonOneFile.setText(Messages.getString("BeetlzSkeletonGui.printOneFile")); //$NON-NLS-1$
          GridData buttonOneFileLData = new GridData();
          buttonOneFile.setLayoutData(buttonOneFileLData);
          buttonOneFile.setSelection(false);
        }
        {
          buttonAllFiles = new Button(groupSkeletonOutput, SWT.RADIO | SWT.LEFT);
          buttonAllFiles.setText(Messages.getString("BeetlzSkeletonGui.printSeparateFiles")); //$NON-NLS-1$
          GridData buttonAllFilesLData = new GridData();
          buttonAllFilesLData.widthHint = 142;
          buttonAllFilesLData.heightHint = 21;
          buttonAllFiles.setLayoutData(buttonAllFilesLData);
          buttonAllFiles.setSelection(false);
        }
      }
      {
        buttonUseBasics = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseBasics.setText(Messages.getString("BeetlzGui.useBasicSettings")); //$NON-NLS-1$
        FormData buttonUseBasicsLData = new FormData();
        buttonUseBasicsLData.width = 140;
        buttonUseBasicsLData.height = 21;
        buttonUseBasicsLData.left =  new FormAttachment(0, 1000, 170);
        buttonUseBasicsLData.top =  new FormAttachment(0, 1000, 77);
        buttonUseBasics.setLayoutData(buttonUseBasicsLData);
        buttonUseBasics.setSelection(action.useBasics);
      }
      {
        buttonNullCheck = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonNullCheck.setText(Messages.getString("BeetlzGui.checkNullity")); //$NON-NLS-1$
        FormData buttonNullCheckLData = new FormData();
        buttonNullCheckLData.width = 116;
        buttonNullCheckLData.height = 21;
        buttonNullCheckLData.left =  new FormAttachment(0, 1000, 19);
        buttonNullCheckLData.top =  new FormAttachment(0, 1000, 77);
        buttonNullCheck.setLayoutData(buttonNullCheckLData);
        buttonNullCheck.setSelection(action.nullCheck);
      }
      {
        buttonCancel = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonCancel.setText(Messages.getString("BeetlzGui.cancel")); //$NON-NLS-1$
        buttonCancel.addListener(SWT.Selection, listener);
        FormData buttonCancelLData = new FormData();
        buttonCancelLData.width = 128;
        buttonCancelLData.height = 28;
        buttonCancelLData.left =  new FormAttachment(0, 1000, 331);
        buttonCancelLData.top =  new FormAttachment(0, 1000, 188);
        buttonCancel.setLayoutData(buttonCancelLData);
      }
      {
        buttonGo = new Button(dialogShell, SWT.PUSH | SWT.CENTER);
        buttonGo.setText(Messages.getString("BeetlzGui.go")); //$NON-NLS-1$
        buttonGo.setData(new Integer(13));
        buttonGo.addListener(SWT.Selection, listener);
            //cancelButton.addListener(SWT.Selection, listener);
        
        
        FormData buttonGoLData = new FormData();
        buttonGoLData.width = 128;
        buttonGoLData.height = 29;
        buttonGoLData.left =  new FormAttachment(0, 1000, 331);
        buttonGoLData.top =  new FormAttachment(0, 1000, 149);
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
        groupSourceLData.width = 138;
        groupSourceLData.height = 90;
        groupSourceLData.left =  new FormAttachment(0, 1000, 181);
        groupSourceLData.top =  new FormAttachment(0, 1000, 130);
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
        buttonPureBonLData.width = 140;
        buttonPureBonLData.height = 23;
        buttonPureBonLData.left =  new FormAttachment(0, 1000, 170);
        buttonPureBonLData.top =  new FormAttachment(0, 1000, 42);
        buttonPureBon.setLayoutData(buttonPureBonLData);
        buttonPureBon.setSelection(action.pureBon);
      }
      {
        buttonUseJml = new Button(dialogShell, SWT.CHECK | SWT.LEFT);
        buttonUseJml.setText(Messages.getString("BeetlzGui.useJml")); //$NON-NLS-1$
        FormData buttonNoJmlLData = new FormData();
        buttonNoJmlLData.width = 116;
        buttonNoJmlLData.height = 17;
        buttonNoJmlLData.left =  new FormAttachment(0, 1000, 19);
        buttonNoJmlLData.top =  new FormAttachment(0, 1000, 42);
        buttonUseJml.setLayoutData(buttonNoJmlLData);
        buttonUseJml.setSelection(action.useJml);
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
      dialogShell.setText(Messages.getString("BeetlzSkeletonGui.skeletonGeneration")); //$NON-NLS-1$
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
