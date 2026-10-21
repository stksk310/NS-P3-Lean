param([Parameter(Mandatory=$true)][string]$Workspace,[string]$Tag='root')
$ErrorActionPreference='Stop'
Set-Location -LiteralPath $Workspace
$env:ELAN_HOME='C:/Users/stksk/.elan'
$env:GIT_CONFIG_COUNT='1'
$env:GIT_CONFIG_KEY_0='safe.directory'
$env:GIT_CONFIG_VALUE_0='*'
function Get-P3SourceHashes {
 $p3paths=@(Get-ChildItem NSP3 -Filter '*.lean' | ForEach-Object {'NSP3/'+$_.Name})+
 @('Main.lean','NSP3.lean','lean-toolchain','lakefile.toml','lake-manifest.json','FIRST_MISSING_THEOREM.lean',
 'diagnostics/verify_symbolic.ps1','diagnostics/verify_symbolic_all_modules.ps1')
 $p3hashes=@{}
 foreach($p3relative in $p3paths){$p3hashes[$p3relative]=(Get-FileHash -LiteralPath $p3relative -Algorithm SHA256).Hash.ToLowerInvariant()}
 return $p3hashes
}
$p3receiptPath="diagnostics/symbolic_${Tag}_receipt.json"
if(Test-Path -LiteralPath $p3receiptPath){throw 'Refusing Tag reuse: preserve existing receipt and choose a fresh Tag'}
$p3sourceBefore=Get-P3SourceHashes
$p3testModules=@(Get-ChildItem NSP3 -Filter '*Test.lean' | Sort-Object Name | ForEach-Object { 'NSP3.'+$_.BaseName })
$p3args=@('build','NSP3')+$p3testModules
& lake @p3args *> "diagnostics/symbolic_${Tag}_build.log"
if($LASTEXITCODE -ne 0){ throw 'Build/tests failed' }
& lake env lean Main.lean *> "diagnostics/symbolic_${Tag}_smoke.log"
if($LASTEXITCODE -ne 0){ throw 'Smoke failed' }
& lake env lean NSP3/Axioms.lean *> "diagnostics/symbolic_${Tag}_axioms.log"
if($LASTEXITCODE -ne 0){ throw 'Axioms failed' }
& lake env lean FIRST_MISSING_THEOREM.lean *> "diagnostics/symbolic_${Tag}_first_missing.log"
if($LASTEXITCODE -ne 0){ throw 'Obligation typecheck failed' }
 $p3sourceAfter=Get-P3SourceHashes
foreach($p3relative in $p3sourceBefore.Keys){if($p3sourceBefore[$p3relative] -ne $p3sourceAfter[$p3relative]){throw 'Source changed during verification'}}
if($p3sourceBefore.Count -ne $p3sourceAfter.Count){throw 'Source inventory changed during verification'}
$p3logHashes=@{}
foreach($p3kind in @('build','smoke','axioms','first_missing')){
 $p3log="diagnostics/symbolic_${Tag}_${p3kind}.log"
 $p3logHashes[$p3log]=(Get-FileHash -LiteralPath $p3log -Algorithm SHA256).Hash.ToLowerInvariant()
}
@{status='PASS'; tag=$Tag; testModules=$p3testModules; targets=$p3args; sourceSha256=$p3sourceAfter; logSha256=$p3logHashes;
  completedUtc=[DateTime]::UtcNow.ToString('o')} | ConvertTo-Json -Depth 5 |
  Out-File -Encoding utf8 $p3receiptPath
Write-Output "PASS $Tag full build, $($p3testModules.Count) test modules, smoke, axioms, obligation typecheck"
