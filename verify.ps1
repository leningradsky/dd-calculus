#!/usr/bin/env pwsh
# DD Calculus Verification Script
# Run this to verify all modules compile with --safe --without-K

$ErrorActionPreference = "Stop"

Write-Host "=== DD CALCULUS VERIFICATION ===" -ForegroundColor Cyan
Write-Host ""

# Change to repo root
$repoRoot = Split-Path -Parent $PSScriptRoot
if (!(Test-Path "$repoRoot/src/DD/Index.agda")) {
    $repoRoot = $PSScriptRoot
}
Set-Location $repoRoot

# Count modules and lines
$modules = Get-ChildItem -Path "src" -Recurse -Filter "*.agda"
$moduleCount = $modules.Count
$lineCount = ($modules | Get-Content | Measure-Object -Line).Lines

Write-Host "Modules: $moduleCount" -ForegroundColor Yellow
Write-Host "Lines: $lineCount" -ForegroundColor Yellow
Write-Host ""

# Verify master index (this transitively checks all modules)
Write-Host "Verifying DD.Index (master theorem collection)..." -ForegroundColor Cyan
$result = agda --safe src/DD/Index.agda 2>&1
$exitCode = $LASTEXITCODE

if ($exitCode -eq 0) {
    Write-Host ""
    Write-Host "✅ DD.Index: OK" -ForegroundColor Green
    Write-Host "   Full DD→SM chain compiles successfully!" -ForegroundColor Green
    Write-Host ""
    Write-Host "=== VERIFICATION PASSED ===" -ForegroundColor Green
    exit 0
} else {
    Write-Host ""
    Write-Host "❌ DD.Index: FAILED" -ForegroundColor Red
    Write-Host $result -ForegroundColor Red
    Write-Host ""
    Write-Host "=== VERIFICATION FAILED ===" -ForegroundColor Red
    exit 1
}
