@echo on
@rem Pushbutton installation of VeriFast dependencies.
@rem 
@rem WARNING: creates files/directories in c:\, such as c:\cygwin and c:\OCaml

set VF_OPAM_EXE_DIR=%TEMP%
set VF_CYGWIN_DIR=c:/cygwin64
bitsadmin.exe /transfer "opam" https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-windows.exe %VF_OPAM_EXE_DIR%\opam.exe || exit /b 1
%VF_OPAM_EXE_DIR%\opam init --help

@rem First, list pre-installed packages
%VF_CYGWIN_DIR%\bin\bash -lc "cygcheck -c -d" 

bitsadmin.exe /transfer "cygwin" https://www.cygwin.com/setup-x86_64.exe %TEMP%\setup-cygwin.exe || exit /b 1
%TEMP%\setup-cygwin.exe -B -qnNd -R %VF_CYGWIN_DIR% -l %VF_CYGWIN_DIR%/var/cache/setup -s https://ftp.snt.utwente.nl/pub/software/cygwin/ -P p7zip -P cygutils-extra -P mingw64-x86_64-gcc-g++ -P make -P patch -P rlwrap -P libreadline6 -P diffutils -P wget -P cmake -P ninja || exit /b 1

@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions
echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > %VF_CYGWIN_DIR%\etc\fstab || exit /b 1

%VF_OPAM_EXE_DIR%/opam init -y --cygwin-local-install --cygwin-location %VF_CYGWIN_DIR% || exit /b 1
%VF_OPAM_EXE_DIR%/opam install -y lablgtk || exit /b 1

for /f "TOKENS=* USEBACKQ" %%f in (`cd`) do set VFWORKDIR=%%f

%VF_CYGWIN_DIR%\bin\bash -lc "cd ""$VFWORKDIR"" && bash setup-windows.sh" || exit /b 1
