declare -i filecnt=0
format=$1
declare -i bound=10000
declare -i totalbound=-1
tmpfolder="extract_tmp"
declare -i result=(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
declare -i TOT=0
firstfile=""
lastfile=""

function run_parser {
  for file in "$tmpfolder"/*.der
  do
    TOT=$TOT+1
    filebase=$(basename $file)
    if [ $filecnt -eq 10000 ]; then
      grep -q $filebase data/$format/positive_ignore.txt
      if [ $? -eq 0 ]; then
        result[1]=${result[1]}+1
        echo "Ignored due to white list:" $filebase 
      else 
        ./ASN1_Parser.exe $format "$file" > /dev/null
        ret=$?
	result[$ret]=${result[$ret]}+1
      fi
    else
      ./ASN1_Parser.exe $format "$file" > /dev/null
      ret=$?
      result[$ret]=${result[$ret]}+1
    fi
    if [ $(expr $TOT % 1000) -eq 0 ]; then
      echo Processed "$TOT": $file
    fi
    if [ $TOT -eq 1 ]; then
      firstfile=$filebase
    fi
    lastfile=$filebase
  done
  rm -rf $tmpfolder
}

rm -rf $tmpfolder
mkdir $tmpfolder
for folder1 in scan/*
do
  for folder2 in $folder1/*
  do
    for file in $folder2/*.results
    do
      out="$tmpfolder"/"$(basename $file)"
      ./extractor/extract $file $out > /dev/null 2> /dev/null
      filecnt=$filecnt+1
      if [ $(expr $filecnt % $bound) -eq 0 ]; then
        run_parser
        mkdir $tmpfolder
      fi
      if [ $filecnt -eq $totalbound ]; then
        break 3
      fi
    done
  done
done

if [ $(expr $filecnt % $bound) -ne 0 ]; then
  run_parser
else
  rm -rf $tmpfolder
fi

echo First: $firstfile
echo Last: $lastfile

echo Total extract: $filecnt

echo Total parser: $TOT

for i in ${!result[@]}; do
  echo Exit with return value "$i": ${result[$i]}
done


