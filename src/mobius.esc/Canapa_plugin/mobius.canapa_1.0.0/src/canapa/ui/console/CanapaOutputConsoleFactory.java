package canapa.ui.console;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleFactory;
import org.eclipse.ui.console.IConsoleManager;

import canapa.CanapaPlugin;

public class CanapaOutputConsoleFactory implements IConsoleFactory{

	public void openConsole() {
		System.out.println("Open console");
		CanapaOutputConsole console = CanapaPlugin.getPlugin().getConsole();
		if (console != null) {
			IConsoleManager manager = ConsolePlugin.getDefault().getConsoleManager();
			IConsole[] existing = manager.getConsoles();
			boolean exists = false;
			for (int i = 0; i < existing.length; ++i) {
				if(console == existing[i])
					exists = true;
			}
			if(! exists)
				manager.addConsoles(new IConsole[] {console});
			manager.showConsoleView(console);
		}
	}

	public static void closeConsole() {
		IConsoleManager manager = ConsolePlugin.getDefault().getConsoleManager();
		CanapaOutputConsole console = CanapaPlugin.getPlugin().getConsole();
		if (console != null) {
			manager.removeConsoles(new IConsole[] {console});
			ConsolePlugin.getDefault().getConsoleManager().addConsoleListener(console);
		}
	}
}
