# For pretty output
color () {
  if [ -t 1 ]; then
    tput setaf $2 || true
    echo $1
    tput sgr0 || true
  else
    echo $1
  fi
}

red () {
  color "$1" 1
}

green () {
  color "$1" 2
}

blue () {
  color "$1" 4
}

magenta () {
  color "$1" 5
}

# [count log-file] displays the number of lines received so far in the terminal,
# while writing its output in log-file
count () {
  i=0
  echo -n > $1
  while read line; do
    echo $line >> $1
    i=$(($i+1))
    echo -ne "\r$i lines of output"
  done
  echo
  blue "log written to $1"
}

# The return value of Bash function is the exit status of their last command;
# therefore, you can do things like [if is_osx; then ...].
is_osx () {
  [[ $(uname) == "Darwin" ]]
}

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

# If a command [cmd] is not found in path, then [success_or cmd msg] prints
# [msg] if non-empty, then aborts with a non-zero exit status.
success_or ()
{
  if ! command -v $1 >/dev/null 2>&1; then
    red "ERROR: $1 not found"
    if [[ $2 != "" ]]; then
      echo "Hint: $2"
    fi
    exit 1
  fi
  echo ... $1 found
}

# [if_yes cmd] prompts the user, and runs [cmd] if user approved, and aborts
# otherwise
prompt_yes ()
{
  if $INTERACTIVE; then
    read ans
    case "$ans" in
      [Yy]|""|"yes")
        $1
        ;;

      *)
        $2
        ;;
    esac
  else
    $1
  fi
}

if_yes ()
{
  echo "Do you want to run: $1? [Yn]"
  prompt_yes "$1" "exit 1"
}

cygwin_has () {
  (( $(cygcheck -c -d $1 | wc -l) > 2 ))
}
