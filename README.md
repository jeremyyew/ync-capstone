# The `proof-reader`
This repository contains all my MCS Capstone AY19/20 project source code and submission files. 

- [The `proof-reader`](#the-proof-reader)
  - [Description](#description)
  - [Report](#report)
  - [Usage](#usage)
  - [Requirements](#requirements)
  - [Setup](#setup)
    - [For Linux and MacOS](#for-linux-and-macos)
    - [For Windows](#for-windows)
    - [Running from source](#running-from-source)
  - [Build process](#build-process)
    - [Building Linux/MacOS executable using PyInstaller](#building-linuxmacos-executable-using-pyinstaller)
    - [Building Windows executable using py2exe and Wine on Linux machine](#building-windows-executable-using-py2exe-and-wine-on-linux-machine)
  - [Testing](#testing)


## Description 
The `proof-reader` tool is a parser that emits two types of warnings corresponding to the syntax issues described in the previous section:

1. Warns user of instances where unpermitted tactics are used.
2. Warns user of instances of incorrect arity in terms supplied to tactics such as "rewrite", "exact", "apply", etc.

`proof-reader` is intended to be used by students, both during proof editing and as a final check before submission. As students are writing proofs, the `proof-reader`  keeps them on the right track by correcting issues that might be affecting their thought process. When used as a final check, it will help them correct proofs that might have been accepted by Coq but do not demonstrate the intended learning goals of the exercise. The `proof-reader` can be used directly on student submissions by the instructor as well. 

## Report
Read the full capstone report here: [submissions/capstone-report-final/jeremy-capstone-submission.pdf](submissions/capstone-report-final/jeremy-capstone-submission.pdf).

## Usage 
To run `proof-reader` on your proof script, simply execute the following Emacs command while in Proof General, with the editor focused on the buffer containing the script: 
```
 M-x jeremy-proof-reader
```

The script will first be re-run from the beginning by Proof General. `proof-reader` will then evaluate the script and display any relevant warnings in the Emacs response buffer, for example:   

```
WARNING: In tactic invocation REWRITE on parent term (Nat.add_assoc a b):
 Term "Nat.add_assoc" with arity 3 incorrectly applied to 2 terms (a),(b).
```
Or, if there are no warnings: 
```
No warnings.
```

## Requirements 
- GNU Emacs 
- Proof General
- Coq 
## Setup
Note: your Emacs init file will be one of three options: `~/.emacs`, `~/.emacs.el`, or `~/.emacs.d/init.el`.
### For Linux and MacOS
(Tested on MacOS Mojave 10.14.6.)
1. Download the executable [dist/linux/proof_reader](dist/linux/proof_reader) and the script [dist/proof-reader.el](dist/proof-reader.el).
2. Insert this line at the bottom of your Emacs init file: `load ("<path/to/proof-reader.el>")`, inserting the location that you saved `proof-reader.el`. 
3. In `jeremy-shell-command-parser` in `proof-reader.el`, insert the path to the `proof_reader` executable in `<path/to/proof_reader>`: 
    ```
    (defun jeremy-shell-command-parser (s)
        "Call proof_reader in shell and display program output as message."
        (progn
        (setq c (concat "<path/to/proof_reader> --input " (shell-quote-argument s)))
        (message (shell-command-to-string c))))
    ```
4. Restart Emacs. 

### For Windows
(Tested on Windows 10 Home.)
Same as Linux/MacOS, except download the executable [dist/windows/proof_reader.exe](dist/windows/proof_reader.exe) instead.

 Warning: the executable does not work yet. I have limited access to a Windows machine.

### Running from source
Requirements: 
- Python3. 
   
Same as Linux/MacOS, except download the [jeremy-parser](jeremy-parser) folder instead, and prefex `"<path/to/proof_reader> --input "` with `python3`, i.e. `"python3 <path/to/proof_reader> --input "`.


## Build process
### Building Linux/MacOS executable using PyInstaller 
```
/Users/Macintosh/.pyenv/shims/python3 -m PyInstaller --onefile jeremy-parser/proof_reader.py
```
### Building Windows executable using py2exe and Wine on Linux machine
Need to use Python 3.6.8 since that is the latest release with an MSI file. 
See https://www.andreafortuna.org/2017/12/27/how-to-cross-compile-a-python-script-into-a-windows-executable-on-linux/.
1. Download https://www.python.org/ftp/python/3.6.8/python-3.6.8-amd64.exe.
2. Install by clicking. 
3. `cd /Users/Macintosh/.wine/drive_c/users/Macintosh/Local\ Settings/Application\ Data/Programs/python/Python36`.
4. `wine python.exe lib/site-packages/pip install pyinstaller`.
5. `wine ~/.wine/drive_c/users/Macintosh/Local\ Settings/Application\ Data/Programs/python/Python36/Scripts/pyinstaller.exe --onefile ~/github/ync-capstone/jeremy-parser/proof_reader.py`

It is much simpler to build from source on a Windows machine. 


## Testing
Requires `deepdiff` package. 
To run the test suite, run: 
```
python3 tests.py
```
If successful: 
```
............................................
----------------------------------------------------------------------
Ran 44 tests in 1.596s

OK
```
To enable logging, uncomment this line in [jeremy-parser/proof_reader.py](jeremy-parser/proof_reader.py)
```
# logging.basicConfig(
#     filename=f'logs/log_{datetime.datetime.now().strftime("%H-%M-%S_%d-%m")}.txt', level=logging.INFO)
```
and comment this line: 
```
logger.setLevel(logging.WARNING)
```
Each test run will write a time-stamped log text file to
[jeremy-parser/logs](jeremy-parser/logs), with low-level information on the parser execution and diffs from expected results.
