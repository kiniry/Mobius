package navmark;

import java.io.*;
import javax.microedition.midlet.*;
import javax.microedition.lcdui.*;
import javax.microedition.rms.RecordStore;
import org.aspectj.lang.annotation.AdviceName;

aspect MarkGUI {
	static private void action(String s) {
		CommPrinter.print("A:" + s + "\r\n");
	}	  

	static private void arg(Object o) {
		CommPrinter.print("-:" + o.getClass().getName() + ":" + o + "\r\n");
	}	  

	static public void callback1(CommandListener l, 
			Command c, Displayable d) {
		action("CallCommandListener");
		arg(l);
		arg(c);
		arg(d);
	};        

	static public void callback2(ItemCommandListener l, 
			Command c, Item i) {
		action("CallItemCommandListener");
		arg(l);
		arg(c);
		arg(i);
	};        
	
		
	pointcut createScreen1() : call(List.new(..));
	pointcut createScreen2() : call(Form.new(..));
	pointcut createScreen3() : call(Alert.new(..));
	pointcut createScreen4() : call(TextBox.new(..));
	pointcut createScreen5() : call(Canvas+.new(..));
	pointcut createCommand() : call(Command.new(..));
	pointcut createCommandListener() : call(CommandListener+.new(..));

	pointcut setScreen(Displayable d) : target(Display) && args(d) &&  call(void setCurrent(Displayable));

	pointcut setCommand(Displayable d, Command c) : target(d) && args(c) && call(void addCommand(Command));
	
	pointcut setCommandListener(Displayable d, CommandListener l) : target(d) && args(l) && call(void setCommandListener(CommandListener));
	
	pointcut notifyDestroyed() : target(MIDlet) && call(void notifyDestroyed());

	/* VERY IMPORTANT WARNING. 
	 * Advices are numbered and their name contain this number in the bytecode.
	 * We will name static real advice based on this numbering.
	 */
	// $1

	public static void tag1(MarkGUI m, Object o, String t) {
		action("Tag");
		arg(o);
		arg(t);
	};        

	after () returning(Object d):  createScreen1() || createScreen2() || createScreen3() 
	                               || createScreen4() || createScreen5()  
	                               || createCommand() || createCommandListener() {
		action("Dummy");
	}

	// $2

	public static void tag2(MarkGUI m, Displayable d, String t) {
		action("SetCurrent");
		arg(d);
		arg(t);
	};
	
	after (Displayable d): setScreen(d) {
		action("Dummy");
	}

	// $3
	before(Displayable d, Command c): setCommand(d,c) {
		action("AddCommand");
		arg(d);
		arg(c);
	};

	// $4
	before(Displayable d, CommandListener l): setCommandListener(d,l) {
		action("AddCommandListener");
		arg(d);
		arg(l);
	};

	// $5
	public static void tag5(MarkGUI m, String t) {
		action("NotifyDestroyed");
		arg(t);
	};
	
	after (): notifyDestroyed() {
		action("Dummy");
	}
}
