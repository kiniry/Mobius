sed 's/\(.*-.*\)-\S*/\1/' | awk '{if ($1==P) S+=$2; else {print P","S; P=$1; S=$2;}}END{print P","S}'
