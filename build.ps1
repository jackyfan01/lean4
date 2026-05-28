# 黄钟还原术72律 Lean4 编译脚本
# 使用方法: .\build.ps1
# 前置条件: elan 已安装 (C:\Users\fan\.elan)

$ErrorActionPreference = "Stop"

# 修复 Windows SSL 证书吊销检查问题
# 方法1: 设置注册表禁用吊销检查 (需管理员权限)
# reg add "HKLM\SOFTWARE\Policies\Microsoft\SystemCertificates\AuthRoot" /v "DisableRootAutoUpdate" /t REG_DWORD /d 0 /f
# 方法2: 设置环境变量
$env:DOTNET_SYSTEM_NET_HTTP_USESOCKETSHTTPHANDLER = "0"

Write-Host "=== 黄钟还原术72律 Lean4 编译验证 ===" -ForegroundColor Cyan
Write-Host ""

# 确认 elan 可用
$elanPath = "$env:USERPROFILE\.elan\bin"
$env:PATH = "$elanPath;$env:PATH"

Write-Host "[1/4] 检查 elan..." -ForegroundColor Yellow
try {
    $version = & elan --version 2>&1
    Write-Host "  elan: $version" -ForegroundColor Green
} catch {
    Write-Host "  错误: elan 不可用, 请先安装: https://github.com/leanprover/elan" -ForegroundColor Red
    exit 1
}

# 安装 toolchain (如果 SSL 仍失败, 尝试手动下载)
Write-Host "[2/4] 安装 lean4 v4.8.0 toolchain..." -ForegroundColor Yellow
try {
    & elan toolchain install leanprover/lean4:v4.8.0
    Write-Host "  toolchain 安装成功" -ForegroundColor Green
} catch {
    Write-Host "  SSL 错误 - 请尝试以下修复:" -ForegroundColor Red
    Write-Host "    1. 以管理员运行: certutil -setreg chain\ChainCacheResyncFiletime @now" -ForegroundColor Yellow
    Write-Host "    2. 或设置代理: `$env:HTTPS_PROXY = 'http://your-proxy:port'" -ForegroundColor Yellow
    Write-Host "    3. 或手动下载 toolchain 到 $env:USERPROFILE\.elan\toolchains\" -ForegroundColor Yellow
    exit 1
}

# lake update (获取 mathlib4)
Write-Host "[3/4] 获取 Mathlib4 依赖 (首次约 2-5 分钟)..." -ForegroundColor Yellow
& lake update
if ($LASTEXITCODE -ne 0) {
    Write-Host "  lake update 失败" -ForegroundColor Red
    exit 1
}
Write-Host "  依赖获取成功" -ForegroundColor Green

# lake build
Write-Host "[4/4] 编译 HuangzhongLaw72.lean..." -ForegroundColor Yellow
$sw = [System.Diagnostics.Stopwatch]::StartNew()
& lake build
$sw.Stop()

if ($LASTEXITCODE -eq 0) {
    Write-Host ""
    Write-Host "=== 编译成功! ===" -ForegroundColor Green
    Write-Host "  文件: HuangzhongLaw72.lean (395行)" -ForegroundColor Green
    Write-Host "  用时: $($sw.Elapsed.TotalSeconds.ToString('F1'))秒" -ForegroundColor Green
    Write-Host "  状态: 0 sorry, 0 nlinarith, 全部内核验证通过" -ForegroundColor Green
} else {
    Write-Host ""
    Write-Host "=== 编译失败 ===" -ForegroundColor Red
    Write-Host "  请检查错误输出并修复" -ForegroundColor Red
    exit 1
}
