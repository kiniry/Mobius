svn log | 
  grep -e "^r[0-9]" | 
  sed 's/^r//' | 
  sort -g |
  awk 'BEGIN{P=0}{print "echo -n \""$5" \"; svn diff -r "P":"$1" | grep -v ^+++ | grep ^+ | wc -l"; P=$1}'
