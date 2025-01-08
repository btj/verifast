$downloadFolder = "C:\temp";
$ownerSlashRepo = "ocaml/opam";
$tag = "2.3.0";

$json = Invoke-Webrequest -Uri "https://api.github.com/repos/$ownerSlashRepo/releases/$tag" -Headers @{'Accept'='application/json'}
$release = $json.Content | ConvertFrom-Json
$release.assets | ?{$_.name -eq 'opam-2.3.0-x86_64-windows.exe'} | %{
    $asset = $_;
    $x = Invoke-Webrequest -Uri $($asset.url) -OutFile "$downloadFolder\$($asset.name)" -Headers @{'Accept'='application/octet-stream'}
}

C:\temp\opam init -y
C:\temp\opam install lablgtk