#!/bin/bash
set -e
SELFDIR="$( realpath "$( dirname "${BASH_SOURCE[0]}" )" )"

jre_link="$SELFDIR/jre"
if [[ ! -e "$jre_link" ]]
then
	selected_jvm_dir=
	for jvm_dir in $(find /usr/lib/jvm -maxdepth 1 -print0 -type d | xargs -0 realpath)
	do
		java_executable="$jvm_dir/bin/java"
		if [[ ! -e "$java_executable" ]]
		then
	 		continue
   	fi

		major_version=$("$java_executable" -version 2>&1 | head -1 | cut -d'"' -f2 | sed '/^1\./s///' | cut -d'.' -f1)
		if [[ "$major_version" -eq "21" ]]
		then
			selected_jvm_dir="$jvm_dir"
			break
		fi

		if [[ "$major_version" -gt "21" ]]
		then
		  # is good, but exact 21 would be better, so keep looking
  		selected_jvm_dir="$jvm_dir"
  	fi
	done

	if [[ "$selected_jvm_dir" == "" ]]
	then
		echo "Found no suitable JRE in /usr/lib/jvm; version >= 21 is required."
		echo "If you have a suitable one installed elsewhere, run"
		echo "  ln -s \"$jre_link\" /path/to/your/jre"
		echo "and then rerun this file."
		exit 1
	fi

	echo "Using JRE in $selected_jvm_dir"
	ln -s "$selected_jvm_dir" "$jre_link"
else
	echo "JRE is already configured to be $(realpath "$jre_link")"
fi
