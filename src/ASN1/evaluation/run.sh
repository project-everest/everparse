format=$1
subfolder=$2
declare -i NCORRECT=0
declare -i TOT=0
declare -i failed=0
for file in data/$format/$subfolder/*.der
do
  filebase=$(basename $file)
  grep -q $filebase data/$format/"$subfolder"_ignore.txt
  if [ $? -eq 0 ]; then
    echo "Ignored due to semantic erros"
  else 
    ./ASN1_Parser.exe $format "$file" > /dev/null
    if [ $? -eq 0 ]; then
      NCORRECT=$NCORRECT+1
    else
      if [ $failed -eq 0 ]; then
        firstfail=$file
      fi
      failed=$failed+1
    fi
    TOT=$TOT+1
    if [ $(expr $TOT % 100) -eq 0 ]; then
      echo Succeeded "$NCORRECT"/"$TOT"
    fi
  fi
done

echo Succeeded "$NCORRECT"/"$TOT"

echo First failure is "$firstfail"
