#!/bin/bash
format=$1
subfolder=$2
declare -i result=(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
declare -i TOT=0
declare -i failed=0
declare -i ignore=0

for file in data/$format/$subfolder/*.der
do
  TOT=$TOT+1
  ignore=0
  filebase=$(basename $file)
  grep -q $filebase data/$format/"$subfolder"_ignore.txt 
  if [ $? -eq 0 ]; then
    result[1]=${result[1]}+1
    echo "Ignored due to white list:" $filebase
    ignore=1
  else 
    if [ "$format" = "CRL" ]; then
      filesize=$(wc -c $file | awk '{print $1}')
      if [ $filesize -ge 100000 ]; then
        result[1]=${result[1]}+1
        echo "Ignored due to filesize:" $filebase
        ignore=1
      fi
    fi
  fi
  if [ $ignore -eq 0 ]; then
    ./ASN1_Parser.exe $format "$file" > /dev/null
    ret=$?
    if [ "$subfolder" = "negative" ]; then
      if [ $ret -ne 0 ]; then
        ret=1
      fi
    fi
    result[$ret]=${result[$ret]}+1
  fi
  if [ $(expr $TOT % 1000) -eq 0 ]; then
    echo Processed "$TOT"
  fi
  if [ $TOT -eq 1 ]; then
    firstfile=$filebase
  fi
  lastfile=$filebase
done

echo First: $firstfile
echo Last: $lastfile

echo Total: $TOT

for i in ${!result[@]}; do
  echo Exit with return value "$i": ${result[$i]}
done


