# Get the list of processes
$processes = Get-Process

# Display the process name and ID
foreach ($process in $processes) {
    Write-Output "Process Name: $($process.Name), ID: $($process.Id)"
}