# This script installs EverParse build dependencies (including Cygwin)
# and builds EverParse.

function global:Invoke-BashCmd
{
    # This function invokes a Bash command via Cygwin bash.
    $Error.Clear()

    Write-Host "Args:" $args

    # Exec command
    $cygpath = c:\cygwin64\bin\cygpath.exe -u ${pwd}
    c:\cygwin64\bin\bash.exe --login -c "cd $cygpath && $args"

    if (-not $?) {
        Write-Host "*** Error:"
        $Error
        exit 1
    }
}

$Error.Clear()
$LastExitCode = 0

$ProgressPreference = 'SilentlyContinue'

# powershell defaults to TLS 1.0, which many sites don't support.  Switch to 1.2.
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

# Switch to this script's directory
Set-Location -ErrorAction Stop -LiteralPath $PSScriptRoot

$Error.Clear()
Write-Host "Install Cygwin with git"
Invoke-WebRequest "https://www.cygwin.com/setup-x86_64.exe" -outfile "cygwinsetup.exe"
cmd.exe /c start /wait .\cygwinsetup.exe --root C:\cygwin64 -P git,wget --no-desktop --no-shortcuts --no-startmenu --wait --quiet-mode --site https://mirrors.kernel.org/sourceware/cygwin/
if (-not $?) {
    $Error
    exit 1
}
Remove-Item "cygwinsetup.exe"

$Error.Clear()
Write-Host "Install and build everparse dependencies"
Invoke-BashCmd "./everest.sh --yes check"
if (-not $?) {
    $Error
    exit 1
}

$Error.Clear()
Write-Host "build everparse"
Invoke-BashCmd "./build-everparse.sh"
if (-not $?) {
    $Error
    exit 1
}

Write-Host "EverParse is now built."
