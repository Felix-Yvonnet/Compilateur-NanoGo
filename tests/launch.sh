#!/usr/bin/env bash

CALL_PATH="$(dirname "$0")"

MSG_EXPECTED_COMPILER="== Expected compiler output =="
MSG_EXPECTED_PROGRAM="== Expected program output =="
NGOC="./ngoc"
ASSEMBLY="gcc -no-pie"


# void launchTest(String filePath)
function launchTest()
{
    FILEPATH="$1"
    FILEPATH_NOEXT="${FILEPATH%.go}"

    echo "Launch ${FILEPATH_NOEXT#"${CALL_PATH}/"}:"

    if grep -q "${MSG_EXPECTED_COMPILER}" "${FILEPATH}"; then

        compareFiles "Compiler output" \
                     <(${NGOC} --type-only "${FILEPATH}" 2>&1) \
                     <(awk "/${MSG_EXPECTED_COMPILER}/,0" "${FILEPATH}" | awk "1;/*\//{exit}" | sed -e '1d;$d')

    elif grep -q "${MSG_EXPECTED_PROGRAM}" "${FILEPATH}"; then

        compareFiles "No compilation error" \
                     <(${NGOC} "${FILEPATH}" 2>&1) \
                     <(echo -ne "")

        compareFiles "No assembly error" \
                     <(${ASSEMBLY} "${FILEPATH_NOEXT}.s" -o "${FILEPATH_NOEXT}" 2>&1) \
                     <(echo -ne "")

        compareFiles "Program output" \
                     <(${FILEPATH_NOEXT}) \
                     <(awk "/${MSG_EXPECTED_PROGRAM}/,0" "${FILEPATH}" | awk "1;/*\//{exit}" | sed -e '1d;$d')

        rm -rf "${FILEPATH_NOEXT}.s"
        rm -rf "${FILEPATH_NOEXT}"
        rm -rf "${FILEPATH_NOEXT}_tast.dot"

    else

        echo -ne " - "
        tput setaf 3; echo -n "WARNING"; tput setaf 7
        echo ": No test was run on this file"

    fi

    echo ""
}


# void compareFiles(String msg, String file, String expectedFile)
function compareFiles()
{
    [[ -n ${FAILED_TEST} ]] && return

    echo -ne " - $1: "

    if DIFF_OUTPUT=$(diff -aB "$2" "$3"); then

        tput setaf 2; echo -n "OK"; tput setaf 7

    else

        tput setaf 1; echo -n "KO"; tput setaf 7

        echo ""
        cat -E <(echo "${DIFF_OUTPUT[0]}")

        FAILED_TEST=true

    fi

    echo ""
}


find "${CALL_PATH}" -name "*.go" -print0 |
    while IFS= read -r -d '' FILE; do

        launchTest "${FILE}"

        [[ -n ${FAILED_TEST} ]] && exit 1;

    done
