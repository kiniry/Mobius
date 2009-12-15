$Id: README.txt,v 1.1.1.1 2002/12/29 12:36:00 kiniry Exp $

This chart provides a mapping between the MONITORING_SYSTEM's BON 
classes and mobius.logging's classes. 

BON Class       mobius.logging Class
---------------------------------------------------------------------------
ASSERTION	Assert
CHECKER		Utilities and Debug via the Assert class
COLLECTOR	Collect and SimpleCollect
EVENT		Event
LEVEL		notion of level in mobius.logging
LOG		provided in the various implementations of DebugOutput
LOGGER		DebugOutput
MESSAGE		use of Strings in DebugOutput or use of Events
STATISTIC	Statistic
TUNER		Debug
TYPE		notion of type in mobius.logging

