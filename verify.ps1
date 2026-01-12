# DD-Calculus Verification Script
# Run with: .\verify.ps1

$ErrorActionPreference = "Stop"
chcp 65001 | Out-Null

Write-Host "=== DD-CALCULUS VERIFICATION ===" -ForegroundColor Cyan
Write-Host ""

$startTime = Get-Date
$failCount = 0
$passCount = 0

$files = Get-ChildItem -Path "src" -Recurse -Filter "*.agda"
$total = $files.Count

Write-Host "Verifying $total modules..." -ForegroundColor Yellow
Write-Host ""

foreach ($file in $files) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    Write-Host -NoNewline "  $($file.Name)... "
    
    $result = agda --safe $file.FullName 2>&1
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "OK" -ForegroundColor Green
        $passCount++
    } else {
        Write-Host "FAILED" -ForegroundColor Red
        $failCount++
        Write-Host $result -ForegroundColor Red
    }
}

$endTime = Get-Date
$duration = ($endTime - $startTime).TotalSeconds

Write-Host ""
Write-Host "=== SUMMARY ===" -ForegroundColor Cyan
Write-Host "Modules: $total"
Write-Host "Passed:  $passCount" -ForegroundColor Green
if ($failCount -gt 0) {
    Write-Host "Failed:  $failCount" -ForegroundColor Red
} else {
    Write-Host "Failed:  0" -ForegroundColor Green
}

$lineCount = ($files | Get-Content | Measure-Object -Line).Lines
Write-Host "Lines:   $lineCount"
Write-Host "Time:    $([Math]::Round($duration, 2))s"
Write-Host ""

if ($failCount -eq 0) {
    Write-Host "✅ ALL MODULES VERIFIED" -ForegroundColor Green
    exit 0
} else {
    Write-Host "❌ VERIFICATION FAILED" -ForegroundColor Red
    exit 1
}
