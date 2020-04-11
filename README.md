# The `proof-reader`
This repository contains all my MCS Capstone AY19/20 project source code and submission files. 
## Requirements 
- GNU Emacs 
- Proof General
- Coq 
## Setup
Note: your Emacs init file will be one of three options: `~/.emacs`, `~/.emacs.el`, or `~/.emacs.d/init.el`.
### For Linux and MacOS
1. Download the executable [dist/linux/proof_reader](dist/linux/proof_reader) and the script [dist/proof-reader.el](dist/proof-reader.el).
2. Insert this line at the bottom of your Emacs init file: `load ("<path/to/proof-reader.el>")`, inserting the location that you saved `proof-reader.el`. 
3. In `jeremy-shell-command-parser` in `proof-reader.el`, insert the path to the `proof_reader` executable in `<path/to/proof_reader>`: 
    ```
    (defun jeremy-shell-command-parser (s)
        "Call proof_reader in shell and display program output as message."
        (progn
        (setq c (concat "./<path/to/proof_reader> --input " (shell-quote-argument s)))
        (message (shell-command-to-string c))))
    ```
4. Restart Emacs. 

### For Windows
Same as Linux/MacOS, except download the executable [dist/windows/proof_reader.exe](dist/windows/proof_reader.exe) instead, and replace `"./<path/to/proof_reader> --input "` with `"/<path/to/proof_reader> --input "` (omit the leading period).
## Build commands
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

## Usage


## Testing
To run the test suite...

Each test run will generate a time-stamped log text file in
[jeremy-parser/logs](jeremy-parser/logs), with low-level information on the parser execution and diffs from expected results.

# To do: 
- [ ] Appendix.
- [ ] Testimonials.
