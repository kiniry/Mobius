package Ambit;

import java.awt.*;
import java.applet.*;

import Ambit.Console;
import Ambit.Productions;

public class AmbitApplet extends Applet {
    
    Console console;
    
	void resetButton_Clicked(Event event) {
        console.resetState();
	}

	void showButton_Clicked(Event event) {
        console.showState("");
	}

	void runButton_Clicked(Event event) {
        console.execAgent();
	}

	public void init() {
		super.init();

		// Take out this line if you don't use symantec.itools.net.RelativeURL
        symantec.itools.lang.Context.setDocumentBase(getDocumentBase());

		//{{INIT_CONTROLS
		setLayout(null);
		addNotify();
		resize(496,304);
		txtOutput = new java.awt.TextArea(8,80);
		txtOutput.reshape(8,112,480,160);
		txtOutput.setFont(new Font("Courier", Font.PLAIN, 12));
		add(txtOutput);
		runButton = new java.awt.Button("Run");
		runButton.reshape(88,280,96,16);
		runButton.setFont(new Font("Dialog", Font.BOLD, 12));
		add(runButton);
		showButton = new java.awt.Button("Show");
		showButton.reshape(200,280,96,16);
		add(showButton);
		resetButton = new java.awt.Button("Reset");
		resetButton.reshape(312,280,96,16);
		add(resetButton);
		txtInput = new java.awt.TextArea(4,80);
		txtInput.reshape(8,8,480,96);
		txtInput.setFont(new Font("Courier", Font.PLAIN, 12));
		add(txtInput);
		//}}

		console = new Console();
        console.setupIO(txtInput, txtOutput);
        new Productions().setup(console);
	}

	public boolean handleEvent(Event event) {
		if (event.target == runButton && event.id == Event.ACTION_EVENT) {
			runButton_Clicked(event);
			return true;
		}
		if (event.target == showButton && event.id == Event.ACTION_EVENT) {
			showButton_Clicked(event);
			return true;
		}
		if (event.target == resetButton && event.id == Event.ACTION_EVENT) {
			resetButton_Clicked(event);
			return true;
		}
		return super.handleEvent(event);
	}

	//{{DECLARE_CONTROLS
	java.awt.TextArea txtOutput;
	java.awt.Button runButton;
	java.awt.Button showButton;
	java.awt.Button resetButton;
	java.awt.TextArea txtInput;
	//}}
}
