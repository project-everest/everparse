# F* VS Code Assistant

This VS Code extension provides support for interactively editing and
checking F* files incrementally.

## Installation

An release is available on the VSCode marketplace: https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant

You need to have a working F* installation, where `fstar.exe` and `z3` are in your path.

Use the latest release of F*: https://github.com/FStarLang/FStar/releases/tag/v2024.01.13

If you have installed F* or Z3 using opam, make sure you start VS Code from inside the opam environment after running `eval $(opam env)`.
If you are using WSL, the WSL plugin for VS Code will run your `bashrc`, and it is enough to put the `eval $(opam env)` there.
(When only Z3 is missing, you will get a message like `ERROR: F* flycheck process exited with code 1`.)

The command `fstar.exe --ide A.fst` should print the following protocol-info (Look at the full strig, it ends with ""full-buffer","format","restart-solver", "cancel"]}".

```json
{"kind":"protocol-info","version":2,"features":["autocomplete","autocomplete/context","compute","compute/reify","compute/pure-subterms","describe-protocol","describe-repl","exit","lookup","lookup/context","lookup/documentation","lookup/definition","peek","pop","push","search","segment","vfs-add","tactic-ranges","interrupt","progress","full-buffer","format","restart-solver", "cancel"]}
```

## Features and basic usage guide

### Basic syntax highlighting

The extensions highlights all keywords in an F* source file, triggered on .fst and fsti files

### Incremental checking

The main feature offered by this extension is to incrementally check the contents of an F* document.

There are three forms of checking:

  * Light checking: Where F* checks the basic well-formedness of a program, but
    without proving that it is fully type correct. This form of checking is sufficient
    to detect basic typing errors, e.g., treating an integer as a string. Note, 
    light checking corresponds to checking a definition with `--lax`. This form of 
    lax checking is sometimes useful if a user wants to quickly skip past a part of the
    document that they will verify fully later.

  * Fly checking: Where F* implicitly light-checks the document every time the document changes.

  * Full checking: Where F* typechecks a program and proves it correct.

This extension launches two F* processes for each document: One for fly-checking
and another for explicit user-triggered checking requests.

For each line of the document for which the user explicitly requested checking
F* indicates the checking status with an icon in the gutter on the left of the editor pane, 
as illustrated by the screenshot below.

![Screenshot](resources/screenshot.png)

The screenshot shows two documents in various states of checking:

1. In progress: On the left, a prefix of the document has an hourglass in the gutter. These lines
   are currently being checked by F*.

2. Scheduled: The next few lines are marked with "..." in the gutter. These lines are scheduled to be
   checked by F* after the in-progress lines are finished, if they finish successfully. In this case, 
   the user has asked to check the document until the last line marked with "...". F* will check the
   document up to the definition that encloses the last line that the user requested.

3. Fully checked: On the right, a prefix of the document has a green dashed line in the gutter. These 
   lines have been fully verified.

4. Light checked: On the right, the next few lines have a blue dashed line in the gutter. These lines
   were processed by F*, but the user instructed F* to only light check it. As you can see, these
   lines are not actually proven correct by F* (e.g., `let x : nat = -1` is accepted). You can choose to
   disable displaying this blue line indicator in the user settings (see below).

5. Fully checked with light prefix: The rest of the document on the right has been checked, however
   since it follows some lines that have been admitted, you should be wary of the verification result.
    
#### Basic Navigation

* Fly-check on opening: When a file is opened, F* will, by default, 
  fly-check the entire entire contents of the file,
  stopping at the first error. Any errors will be reported in the problem pane
  and as "squigglies". Symbols are resolved and hover and jump-to-definition
  tools should work.

* F*: Check to position: The key-binding `Ctrl+.` advances the checker up to the
  F* definition that encloses the current cursor position, fully checking.

* F*: Light check to position: The key-binding `Ctrl+Shift+.` advances the checker by
  light-checking the document up to the F* definition enclosing the current cursor position.
  This is useful if you want to quickly advance the checker past a chunk of document which
  might otherwise take a long time to check.

* F*: Restart: The key-binding `Ctrl+; Ctrl+.` restarts the F* session for the current document,
  rewindind the checker to the top of the document and rescanning it to load any dependences
  that may have changed, and fly-checking it to load symbols.

* Check file on save: When the file is saved, or when doing `Ctrl+s`, the
  checker is advanced in full checking mode to the end of the document.
  This is equivalent to doing `Ctrl+.` on the last line of the document.

Note, although checking the document proceeds in a linear, top-down fashion, at no point is any
fragment of the document locked. You can keep editing a document while F* is checking some prefix 
of it.

#### Settings

You can reconfigure some of the behavior of the extension in the "User Settings" menu of VSCode.

Launch the command pallette using `Ctrl+Shift+p`.

Search for User Settings and then for `F* VSCode Assistant` in the `Extensions` category.

You can change the following:

  * verifyOnOpen: Set this flag to fully check a file when it is opened

  * flyCheck: You can choose whether or not F* should implicitly flycheck a document
    when it is opened, at every key stroke, and when it is closed.

  * debug: Set this flag to have the extension log debug information to the console.

  * showLightCheckIcon: You can choose to not show the gutter icon when F* has only light-checked a fragment

You can also change the keybindings:

In the command pallete, search for "F*" and you can see the commands supported there
and view or edit the current key bindings.

### Diagnostic squigglies for errors and warnings

Any errors or warnings reported by the checker appear in the Problems pane and are also
highlighted with "squigglies" in the document.

### Hover for the type of a symbol under the cursor and jump to definitions

You can hover on an identifer to see its type.

If F* can resolve the symbol, you should see its fully qualified name and type.

You can also jump to the definition, using ctrl+click or by pressing F12.

### Proof state dumps for tactic execution

If you are using tactics, you can hover on tactic line to see the last proof state dumped at that line.

### Completions

The extension will suggest auto-completions as you type, based on the symbol resolution in the
current open namespaces in the document. These completions show up in the completion window as
"Method type": a small cube icon precedes them. 

Additionally, vscode provides default name completions based on heuristic syntactic matches
for symbols in the current workspace. These completions show up in the completion window as
"Text type": an "abc" icon precedes them. These are not necessarily reliable, i.e., a name
suggested as a text completion may not actually exist in the current scope.

#### Limitations

Completions only work on fully qualified names. If you have a module abbreviation
`module L = FStar.List.Tot` and type `L.ma` this will *not* complete, since the auto-complete
feature of the F* server does not resolve module abbreviations. 

Auto-completion also does not resolve module inclusion. So, if you type `FStar.List.Tot.ma` this also
will not complete, since `map` is defined in the included module `FStar.List.Tot.Base.map`. If you 
type `FStar.List.Tot.Base.m` this will complete.

Improvements to remove these limitations are most welcome.

### Format document and format selection

You can select a fragment and use the menu option to ask F* to format it.
You can also format the entire document using F*'s pretty printer.

Note: The formatting feature needs to be improving F*'s pretty printer. It doesn't always produce
the nicest looking code. 

### Interrupting or Killing the Prover

Sometimes, a proof can take a long time for Z3 to check. If you want to abandon 
the proof search you can kill the underlying Z3 process and ask F* to restart it.
The following command does that for you:

* fstar-vscode-assistant/kill-and-restart-solver (Ctrl+; Ctrl+c): Terminates the Z3 proof
  search for the current function but maintains the proved status of the file up to that point.

Also, if you're working on F* itself, sometimes it is useful to kill all the F* processes
associated with an editor session, so you can rebuild fstar.exe. 

* fstar-vscode-assistant/kill-all (Ctrl+; Ctrl+Shift+c): Will kill and F* processes (and
  their sub-processes) for all documents. If you want to resume checking a document, you need to
  restart F* for that document by using the Restart command (Ctrl+; Ctrl+.)

### Workspace folders

If you have a .fst.config.json file in a folder, you can open the folder as a workspace
and all F* files in that workspace using the .fst.config.json file as the configuration
for launching `fstar.exe`. Here is a sample .fst.config.json file:

```json
{ "fstar_exe":"fstar.exe",
  "options":["--cache_dir", ".cache.boot", "--no_location_info", "--warn_error", "-271-272-241-319-274"],
  "include_dirs":["../ulib", "basic", "basic/boot", "extraction", "fstar", "parser", "prettyprint", "prettyprint/boot", "reflection", "smtencoding", "syntax", "tactics", "tosyntax", "typechecker", "tests", "tests/boot"] }
```

* The field `"fstar_exe"` contains the path to the `fstar.exe` executable.
* The `"options"` field contains the command line options you want to pass to `fstar_exe`
* The `"include_dirs"` field contains all include directories to pass to `fstar_exe`,
  relative to the workspace root folder.

You can reference environment variables in the config file and the extension will
expand those variables to their values in the current process' environment. Environment
variables are strings of upper-case letters, numbers, and the `_` character. References to them 
are prefixed with `$` and optionally enclosed with `{}`. See below for an example.

```
{ "fstar_exe":"fstar.exe",
  "options":["--cache_dir", ".cache.boot"],
  "include_dirs":["${HOME}/fstar_playground", $USER_PROFILE/workspace] }
```

You can open multiple workspace folders, each with their own config file which applies only 
to files within that folder.

Additionally, you can open a single top-level workspace folder with multiple .fst.config.json file
in several sub-directories, though only one .fst.config.json per directory. When opening a given file,
the extension uses the .fst.config.json file closest to the file in the directory hierarchy.

For example, if you have the following:

```
workspace_root/
├─ dir_A/
│  ├─ A.fst
|
├─ dir_B/
│  ├─ B.fst
|  ├─ B.fst.config.json
├─ Project.fst.config.json
├─ Main.fst
```

Then, `Project.fst.config.json` applies to `Main.fst` and `A.fst`,
while `B.fst.config.json` applies to `B.fst`.


### Working with the vscode remote ssh extension

This extension (by default) works well with the
[vscode remote ssh extesion](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-ssh).
The remote ssh extension enables working on remote files and folders
on a local vscode client. If `fstar.exe` is in path on the remote machine,
then the F* extension works seamlessly on the remote files.

Steps to configure the remote ssh extension are given in detail
[here](https://code.visualstudio.com/docs/remote/ssh). At a high-level:

- Configure key-based authentication on the ssh server. The advantage of
  this step is that logging-in will not require password.
	[This page](https://code.visualstudio.com/docs/remote/troubleshooting#_configuring-key-based-authentication)
	describes setting up key based authentication in detail.

	One caveat for cygwin-based setup is that the client (referred to as "machine" in the page above)
	may have two ssh keys: one in the windows file system and one in the cygwin file system.
  I setup authentication for both (i.e., both the steps under
	"Authorize your macOS or Linux machine to connect" from within the cygwin client
	and steps under "Authorize your Windows machine to connect" within powershell).

- Install the remote ssh extension in vscode.
  In the activity bar, a new icon for "Remote Explorer" appears.

- Click on that "Remote Explorer" icon, and then on the `+` sign next to the `SSH` under remote explorer.

- In the command palette, type `ssh username@host` and press Enter.

- It will then ask for the SSH configuration file to update, I chose the first one it showed me
  (e.g., `C:\Users\aseemr\.ssh\config`).

- This step is a "hack" that you may have to do if your username on the remote machine is
  different from the local username. When trying to connect
	(by pressing the connect button on the dialog box at the botton right after selecting the config file),
	the extension may use the local username and hence will fail.

	One way to get around this is by changing the config file from:

	```
	Host <hostname>
  HostName <hostname>
  User <username>
  ```

	to

	```
	Host <username>@<hostname>
  HostName <hostname>
  User <username>
  ```

	Note the change in the first line to explicitly add the remote username.

  Reload the window after doing this, so that this config appears under the SSH connections in the explorer.
	And then connecting works fine.

- Once connected, we can open folders, files, work with F* as usual.
  Make sure F* is in path on the remote machine.

#### Some troubleshooting

If you keep getting ENOENT error in vscode for fstar.exe, meaning that the extension is unable to find fstar.exe on the remote host,
and you have added F* path on the remote host, try restarting the vscode ssh server (`Ctrl+Shift+P Remote-SSH: Kill VS Code Server on Host`).

## Planned features

This extensions does not yet support the following features, though support is expected soon.

* Evaluating code snippets on F*'s reduction machinery
* Types of sub-terms
* Tactic proof state dumps when there is more than one dump associated with a line, e.g., in loops

## Limitations

This extension does not yet support various themes, e.g., it does not provide different
icons for use in light mode vs. dark mode.

Also, a disclaimer: This is my first non-trivial VSCode extension and I may well not be following
conventions that extension users may expect. Any contributions or suggestions to bring it more in
line with existing conventions are most welcome.

## Running it in development mode

- Run `npm install` in this folder. This installs all necessary npm
  modules in both the client and server folder

- Make sure to have a working fstar.exe in your path

- Open VS Code on this folder.

- Press F5 to build the extension and run it in a new vscode window with the built extension.

## Acknowledgements

The vsfstar extension was also a source of inspiration and initial guidance:
https://github.com/artagnon/vsfstar
