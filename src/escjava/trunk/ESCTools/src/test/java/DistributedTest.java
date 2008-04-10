import junit.framework.*;
import junitutils.*;

public class DistributedTest extends junitutils.TestFilesTestSuite {

    static public junit.framework.Test suite() {

	String hostName = "";
try
{
	java.net.InetAddress localMachine =
java.net.InetAddress.getLocalHost();	
	hostName = localMachine.getHostName();
}
catch(java.net.UnknownHostException uhe)
{
	uhe.getStackTrace();
	hostName = "localhost";
}    
    	String defaultSettings = "-nowarn Deadlock -verboseTrace -testMode -Loop5";
    	String listOfFiles = "src/test/list.txt";
    	String testSuiteName = "Distributed-Test-" + hostName;

	String[] serverNames = {"arrow.ucd.ie","object.ucd.ie"};
	int numberOfServers = serverNames.length;
	int serverIndex = -1; // run no tests unless a match is found

	// Match server name and take every nth test
	for (int i=0; i < serverNames.length; i++)
	{
		if (hostName.equals(serverNames[i])) {
			System.out.println("Test Server: " + hostName);
			serverIndex = i;
			break;
	
		}
	}
	

        junit.framework.TestSuite suite =
	    new AbstractDistributedTestSuite(
		testSuiteName,
		listOfFiles,
		defaultSettings,
		escjava.Main.class,
		serverIndex,
		numberOfServers) {
		    public int expectedIntegerStatus(String f, String o) {
			if (javafe.util.ErrorSet.errors > 0) return 2;

			return 0;
		    }
                    public String expectedStatusReport(String fileToTest,
                        int ecode, String expectedOutput) {
                        int ret = expectedIntegerStatus(fileToTest,expectedOutput);
                        if ((ecode > 0) == (ret > 0)) return null;
                        return super.expectedStatusReport(fileToTest,ecode,expectedOutput);
                    }
		};
	return suite;
    }
}
