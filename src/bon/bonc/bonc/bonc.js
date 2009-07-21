/* Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */

var fs = new ActiveXObject("Scripting.FileSystemObject");

if (WScript.Arguments.length != 3) {
  WScript.StdOut.Write("Script error.");
  WScript.Quit();
}

var java = WScript.Arguments.Item(0);
var bonHome = WScript.Arguments.Item(1);

var jars = new Array("BON.jar", "antlr-runtime-3.0.1.jar", "antlr-2.7.7.jar", "CommandlineParser.jar", "stringtemplate.jar", "prefuse.jar", "google-collect-1.0-rc2.jar");
var classPath = ".";

for (var i=0; i < jars.length; i++) {
  var path = bonHome + ".\\lib\\" + jars[i];
  if (!fs.FileExists(path)) {
    WScript.StdOut.Write("Missing required library: " + jars[i] + ". Exiting.");
    WScript.Quit();
  } else {
    classPath += ";" + path;
  }
}

var args = WScript.Arguments.Item(2);

var shell = new ActiveXObject("WScript.shell")
var out = shell.Exec(java + " -cp " + classPath + " ie.ucd.bon.Main " + args);

while (out.Status == 0) {
     WScript.Sleep(50);
}

WScript.StdOut.Write(out.StdOut.readAll());
