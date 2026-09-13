# The chapter headers of the unit upstream's build/compile.ps1 builds, for each
# program path read from stdin, using the checkout's own resolver:
#
#   ... | pwsh -NoProfile -File tools/r2_headers.ps1 -Checkout <checkout>
#
# One line per program: <path> TAB OK TAB h1|h2|...  or  <path> TAB THROW TAB why
#
# The same calls compile.ps1 makes -- Resolve-CiteOrder with SeedSeen taken from
# the source's own Quire--Name headers -- and the headers Format-CiteChapters
# writes: each resolved chapter's first header as Quire--Name, any later ones
# as written, then the program's own headers. tools/resolver_agree.py compares
# these against `bundle one`.
param([Parameter(Mandatory=$true)] [string]$Checkout)
$ErrorActionPreference = 'Stop'
$Checkout = (Resolve-Path $Checkout).Path
. (Join-Path $Checkout 'build/quire-map.ps1')

foreach ($root in [Console]::In.ReadToEnd().Split("`n")) {
    $root = $root.Trim()
    if (-not $root) { continue }
    try {
        $srcLines = [System.IO.File]::ReadAllLines($root)
        $seedSeen = @{}
        foreach ($l in $srcLines) {
            if ($l -match '^Chapter:\s*(\w+)--(.+?)\s*$') { $seedSeen["$($matches[1])::$($matches[2])"] = $true }
        }
        $ordered = Resolve-CiteOrder -RootLines $srcLines -Repo $Checkout -SeedSeen $seedSeen
        $hs = [System.Collections.Generic.List[string]]::new()
        foreach ($entry in $ordered) {
            $renamed = $false
            foreach ($l in $entry.Lines) {
                if ($l -match '^Chapter:\s*(.+?)\s*$') {
                    if (-not $renamed) { $hs.Add("$($entry.Quire)--$($matches[1])"); $renamed = $true }
                    else { $hs.Add($matches[1]) }
                }
            }
        }
        foreach ($l in $srcLines) {
            if ($l -match '^Chapter:\s*(.+?)\s*$') { $hs.Add($matches[1]) }
        }
        [Console]::Out.WriteLine("$root`tOK`t$($hs -join '|')")
    } catch {
        [Console]::Out.WriteLine("$root`tTHROW`t$($_.Exception.Message -replace '\s+', ' ')")
    }
}
