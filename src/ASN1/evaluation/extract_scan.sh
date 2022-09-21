
if [ $# -ne 1 ] ; then
  echo "Usage : extract_scan n"
  echo "        n : maximum number of files to be extracted"
  exit 1
fi

declare -i bound=$1

declare -i filecnt=0

for folder1 in scan/*
do
  for folder2 in $folder1/*
  do
    for file in $folder2/*.results
    do
      out="$(basename $file)" 
      echo $out
      ./extractor/extract $file tmp/$out
      filecnt=$filecnt+1
      if [ $filecnt -ge $bound ]; then
        break 3
      fi 
    done
  done
done
