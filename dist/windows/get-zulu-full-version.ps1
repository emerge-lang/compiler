Param(
    [parameter(Position=0)]
    [String]
    [ValidateNotNullOrEmpty()]
    $JreDir
)

$release_data = Get-Content "$JreDir\release" | ConvertFrom-StringData
$full_version_with_quotes = $release_data.IMPLEMENTOR_VERSION.TrimStart().TrimEnd()
$full_version = $full_version_with_quotes.substring(1, $full_version_with_quotes.length - 2)
return $full_version