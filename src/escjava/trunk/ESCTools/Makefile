##
## author: David Cok - 26 March 2003
##


# List subprojects in the order in which they should
# be build.  Javafe must be first.
SUBDIRS = Javafe Escjava


all clean build test:
	for d in $(SUBDIRS) ; do \
	    $(MAKE) -C $$d $@ ;\
	done
