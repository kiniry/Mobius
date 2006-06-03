/*
 * Created on Mar 31, 2005
 *
 */
package coqPlugin.prooftask.util;



import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;

import coqPlugin.PreferencePage;

/**
 * @author jcharles
 */
public class CoqDialog extends Dialog{
	List l;
	Text txt;
	String selection = "";
	String [] str;
	String repos = "";
	public CoqDialog(String repos) {
		super(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell());
		
		
		
		//setTitle("Choose the Coq tactic to apply.");
		
		
	}
	
	protected Control createDialogArea(Composite parent) {
		// create a composite with standard margins and spacing
		GridData data;
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 4;
		layout.marginHeight = 10;
		layout.marginWidth = 10;
		composite.setLayout(layout);
		composite.setLayoutData(new GridData(GridData.FILL_BOTH));
		Label lbl = new Label(composite, SWT.NONE);
		lbl.setText("Choose a tactic:");
		
		l = new List(composite, SWT.SINGLE | SWT.V_SCROLL);
		l.getVerticalBar().setVisible(true);
		data = new GridData();
		data.horizontalAlignment = GridData.FILL;
		data.horizontalSpan = 4;
		l.setLayoutData(data);
		l.add("lightAutoJack.");
		l.add("toughAutoJack.");
		File f= new File(PreferencePage.getCoqSemiAuto());
		if (f.exists()) {
			try {
				LineNumberReader r = new LineNumberReader(new FileReader(f));
				String str; 
				
				try {
					while((str = r.readLine()) != null)
						l.add(str);
				} catch (IOException e2) {
					e2.printStackTrace();
				}
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			}
		}
		str = l.getItems();
		lbl = new Label(composite, SWT.NONE);
		lbl.setText("Add a tactic:");
		txt = new Text(composite, SWT.BORDER);
		//
		data = new GridData();
		data.horizontalAlignment = GridData.FILL;
		data.horizontalSpan = 3;
		data.grabExcessHorizontalSpace = true;
		txt.setLayoutData(data);
		new Label(composite, SWT.NONE);
		new Label(composite, SWT.NONE);
		Button btn1 = new Button(composite, SWT.PUSH);
		btn1.setText("Add");
		data = new GridData();
		data.horizontalAlignment = GridData.HORIZONTAL_ALIGN_END;
		btn1.setLayoutData(data);
		Button btn2 = new Button(composite, SWT.PUSH);
		btn2.setText("Remove");
		data = new GridData();
		data.horizontalAlignment = GridData.HORIZONTAL_ALIGN_END;
		//data.horizontalSpan = 2;
		btn2.setLayoutData(data);
		//l.getSelectionIndex();
		applyDialogFont(composite);
		btn1.addMouseListener(new MouseListener() {

			public void mouseDoubleClick(MouseEvent e) {
				
			}

			public void mouseDown(MouseEvent e) {
				l.add(txt.getText());
				int i = l.getItemCount();
				l.select(i - 1);
				l.showSelection();
				str = l.getItems();
			}

			public void mouseUp(MouseEvent e) {
				
			}
			
			});
		btn2.addMouseListener(new MouseListener() {

			public void mouseDoubleClick(MouseEvent e) {
				
			}

			public void mouseDown(MouseEvent e) {
				l.remove(l.getSelectionIndex());
				str = l.getItems();
			}

			public void mouseUp(MouseEvent e) {
				
			}
			
			});
		l.addSelectionListener(new SelectionListener(){
			public void widgetSelected(SelectionEvent e) {
				selection = l.getItem(l.getSelectionIndex());
				txt.setText(selection);
				
			}

			public void widgetDefaultSelected(SelectionEvent e) {
				
			}
			
		});
		return composite;
	}

	/**
	 * @return
	 */
	public String getSelection() {
		 
		File f= new File(PreferencePage.getCoqSemiAuto());
		try {
			//Logger.get().println(f.getAbsolutePath());
			PrintStream out = new PrintStream(new FileOutputStream(f));
			for (int i = 0; i < str.length; i++){
				if((!str[i].equals("lightAutoJack.")) &&
						(!str[i].equals("toughAutoJack.")))
					out.println(str[i]);
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		return selection;
	}
	
}
