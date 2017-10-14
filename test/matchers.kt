package matchers

var isNotNull = com.natpryce.hamkrest.Matcher("isNotNull", { it: Any? -> it != null })
var isNull = com.natpryce.hamkrest.Matcher("isNull", { it: Any? -> it == null })