package canapa.ui.console;

import java.io.PrintStream;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleListener;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;

public class CanapaOutputConsole extends IOConsole implements IConsoleListener {

	private IOConsoleOutputStream stream;
	private boolean initialized = false;
	private boolean visible = false;

	public CanapaOutputConsole() {
		super("CANAPA", null);
	}

	protected void init() {
		super.init();

		if (!initialized) {
			stream = newOutputStream();
			initialized = true;
		}
	}

	protected void dispose() {
		super.dispose();
		visible = false;
	}
	
	public void consolesAdded(IConsole[] consoles) {
		System.out.println("Console added");
	}

	public void consolesRemoved(IConsole[] consoles) {
		System.out.println("Console removed");
	}

	private void bringConsoleToFront() {
		IConsoleManager manager = ConsolePlugin.getDefault()
				.getConsoleManager();
		if (!visible) {
			manager.addConsoles(new IConsole[] { this });
			visible = true;
		}
		manager.showConsoleView(this);
	}

	public PrintStream getPrintStream() {
		bringConsoleToFront();
		return new PrintStream(stream);
	}
}
