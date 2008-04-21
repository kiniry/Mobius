# Update the test scripts and authorisations
cd ~/test
svn cleanup
svn update
cp authprogs.conf ../.ssh
cp mvn-all-servers ..
