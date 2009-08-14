package canapa.util;

import java.io.IOException;
import java.io.PrintStream;

import org.eclipse.core.runtime.FileLocator;

import ui.Main;
import canapa.CanapaPlugin;
import canapa.preferences.PreferenceConstants;

public class RunCanapa {

	public static void runCanapaDir(String projectDir) {

		PrintStream tmp = System.out;
		// Redirecting everything to the console
		PrintStream hacked = CanapaPlugin.getPlugin().getConsole()
				.getPrintStream();
		System.setOut(hacked);

	
		String[] params = { "-simplify",
				CanapaPlugin.plugin_dir + "libs/Simplify-1.5.4.exe",
				"-Suggest", "-dir", projectDir };
		Main.main(params);

		System.setOut(tmp);
	}

	public static void runCanapaFile(String file, String classPath) {

		PrintStream tmp = System.out;
		// Teraz wszytsko idzie na konsolê
		PrintStream hacked = CanapaPlugin.getPlugin().getConsole()
				.getPrintStream();
		System.setOut(hacked);

		String simplify = CanapaPlugin.getPlugin().getPluginPreferences()
				.getString(PreferenceConstants.P_SIMPLIFY_FILE);
		if (simplify == null || simplify.length() == 0){
			//by default assume MAC
			simplify = PreferenceConstants.P_SIMPLIFY_CHOICES[2][0];
		}
		String pluginLocation = "";
		try {
			pluginLocation = FileLocator.toFileURL(
					CanapaPlugin.getPlugin().getBundle().getEntry("/"))
					.getPath();
		} catch (IOException e) {

		}
		
		String[] params = { "-simplify", pluginLocation + "libs/" + simplify, "-Suggest", "-file", file,
				"-cp", classPath };
		Main.main(params);

		System.setOut(tmp);
	}
}
