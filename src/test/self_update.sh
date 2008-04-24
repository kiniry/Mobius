# Update the test scripts and authorisations
cd ~/test
svn cleanup
svn update
cp authprogs.conf ../.ssh
chmod +s mvn-all-servers
cp mvn-all-servers ..
chmod +s ../mvn-all-servers