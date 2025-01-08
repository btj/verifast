Invoke-Webrequest -Uri "https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-windows.exe" -OutFile "C:\temp\opam.exe"

C:\temp\opam init -y
C:\temp\opam install lablgtk