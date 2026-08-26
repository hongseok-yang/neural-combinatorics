param(
    [string]$RunDirectory = "lean/verification_runs/s4_long_campaign"
)

$ErrorActionPreference = "Stop"
Set-Location -LiteralPath $PSScriptRoot

$summary = Join-Path $RunDirectory "SUMMARY.txt"
if (Test-Path -LiteralPath $summary) {
    Get-Content -LiteralPath $summary
} else {
    Write-Output "Campaign has not written a summary yet: $summary"
}

$processes = Get-Process -ErrorAction SilentlyContinue |
    Where-Object { $_.ProcessName -in @("lean", "lake") }
if ($processes) {
    Write-Output ""
    Write-Output "Active Lean/Lake processes:"
    $processes | Select-Object Id, ProcessName,
        @{Name="WorkingGiB"; Expression={[math]::Round($_.WorkingSet64 / 1GB, 2)}},
        @{Name="PrivateGiB"; Expression={[math]::Round($_.PrivateMemorySize64 / 1GB, 2)}}
} else {
    Write-Output ""
    Write-Output "Lean/Lake: stopped"
}
