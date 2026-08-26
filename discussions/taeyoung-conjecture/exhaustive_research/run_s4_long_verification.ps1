param(
    [double]$TimeoutHours = 2,
    [int]$Threads = 1,
    [string]$RunDirectory = "lean/verification_runs/s4_long_campaign"
)

$ErrorActionPreference = "Stop"
Set-Location -LiteralPath $PSScriptRoot

if (-not (Test-Path -LiteralPath "experiments/s4_lean_campaign.json")) {
    throw "Missing experiments/s4_lean_campaign.json. Run: python experiments/prepare_all_s4_lean.py"
}

python experiments/run_lean_verification_campaign.py `
    --manifest experiments/s4_lean_campaign.json `
    --run-dir $RunDirectory `
    --timeout-hours $TimeoutHours `
    --threads $Threads

exit $LASTEXITCODE
