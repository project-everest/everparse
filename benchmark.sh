#!/bin/bash
# EverParse SMT Performance Benchmark
#
# Usage:
#   ./benchmark.sh           # full clean build with profiling
#   ./benchmark.sh --quick   # skip clean, reuse .depend
#   ./benchmark.sh --report-only /path/to/log  # just parse an existing log
#
# Produces:
#   - benchmark_profile.log   : raw build output with --query_stats
#   - benchmark_report.txt    : human-readable summary
#   - benchmark_queries.csv   : per-query CSV for analysis

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

QUICK=false
REPORT_ONLY=""
LOG_FILE="benchmark_profile.log"
REPORT_FILE="benchmark_report.txt"
CSV_FILE="benchmark_queries.csv"

usage() {
    echo "Usage: $0 [--quick] [--report-only <logfile>] [--output-dir <dir>]"
    echo ""
    echo "Options:"
    echo "  --quick          Skip clean build; reuse existing .depend"
    echo "  --report-only F  Parse existing log file F and produce report"
    echo "  --output-dir D   Write output files to directory D (default: .)"
    exit 1
}

OUTPUT_DIR="."
while [[ $# -gt 0 ]]; do
    case "$1" in
        --quick) QUICK=true; shift ;;
        --report-only) REPORT_ONLY="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        -h|--help) usage ;;
        *) echo "Unknown option: $1"; usage ;;
    esac
done

mkdir -p "$OUTPUT_DIR"
LOG_FILE="$OUTPUT_DIR/$LOG_FILE"
REPORT_FILE="$OUTPUT_DIR/$REPORT_FILE"
CSV_FILE="$OUTPUT_DIR/$CSV_FILE"

# ── Setup environment ──────────────────────────────────────────────────
setup_env() {
    export OPAMROOT="$SCRIPT_DIR/opt/opam"
    export OPAM_SWITCH_PREFIX="$OPAMROOT/5.3.0"
    export CAML_LD_LIBRARY_PATH="$OPAM_SWITCH_PREFIX/lib/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml/stublibs:$OPAM_SWITCH_PREFIX/lib/ocaml"
    export FSTAR_EXE="$SCRIPT_DIR/opt/FStar/out/bin/fstar.exe"
    export DICE_HOME="$SCRIPT_DIR/opt/FStar/pulse/share/pulse/examples/dice"
    export KRML_HOME="$SCRIPT_DIR/opt/karamel"
    export EVERPARSE_HOME="$SCRIPT_DIR"
    export EVERPARSE_Z3_VERSION=4.13.3
    export PATH="$OPAM_SWITCH_PREFIX/bin:./:$PATH"
}

# ── Build ──────────────────────────────────────────────────────────────
run_build() {
    setup_env

    if [ "$QUICK" = false ]; then
        echo "── Cleaning build artifacts..."
        find src/ -name "*.checked" -delete 2>/dev/null || true
        rm -f .depend .depend.aux .depend.rsp
    fi

    local nproc
    nproc=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

    echo "── Starting build with --query_stats ($(date))..."
    echo "── Using $nproc parallel jobs"

    make -j"$nproc" OTHERFLAGS="--query_stats" 2>&1 | tee "$LOG_FILE"
    local rc=${PIPESTATUS[0]}

    echo ""
    if [ $rc -ne 0 ]; then
        echo "!! Build had errors (exit code $rc)"
    else
        echo "── Build completed successfully"
    fi

    return $rc
}

# ── Generate report ────────────────────────────────────────────────────
generate_report() {
    local log="$1"

    if [ ! -f "$log" ]; then
        echo "Error: log file not found: $log" >&2
        exit 1
    fi

    echo "── Generating report from $log..."

    # Disable errexit for report generation (grep returns 1 on no match)
    set +e

    {
        echo "================================================================"
        echo "  EverParse SMT Benchmark Report"
        echo "  Generated: $(date -Iseconds)"
        echo "  Git commit: $(git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
        echo "  Git branch: $(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo 'unknown')"
        echo "================================================================"
        echo ""

        # ── Overall statistics ─────────────────────────────────────────
        echo "── Overall Statistics ──"
        echo ""

        local n_files
        n_files=$(grep -ac "TOTAL TIME" "$log" 2>/dev/null || echo 0)
        echo "  Files verified:    $n_files"

        grep -a "TOTAL TIME" "$log" \
            | sed 's/.*TOTAL TIME \([0-9]*\) ms.*/\1/' \
            | awk '{sum+=$1; count++}
               END {
                 printf "  Total wall time:   %.1f min (%.0f s)\n", sum/60000, sum/1000
               }'

        grep -a "Query-stats" "$log" | grep "succeeded" \
            | grep -oP 'succeeded in \K[0-9]+' \
            | awk '{sum+=$1; count++}
               END {
                 printf "  Total SMT time:    %.1f min (%.0f s)\n", sum/60000, sum/1000
                 printf "  Total queries:     %d\n", count
                 printf "  Avg query time:    %d ms\n", (count>0 ? sum/count : 0)
               }'

        grep -a "Query-stats" "$log" | grep "succeeded" \
            | grep -oP 'used rlimit \K[0-9.]+' \
            | awk '{sum+=$1; count++}
               END {
                 printf "  Total rlimit used: %.0f\n", sum
                 printf "  Avg rlimit/query:  %.1f\n", (count>0 ? sum/count : 0)
               }'

        local n_failed
        n_failed=$(grep -a "Query-stats" "$log" | grep -c "failed" 2>/dev/null || echo 0)
        echo "  Failed queries:    $n_failed (retried by F*)"

        local n_errors
        n_errors=$(grep -a "Error 19\|Error 17\|Error 66" "$log" | grep -av "warn_error" | wc -l)
        echo "  Verification errs: $n_errors"

        echo ""

        # ── Top files by SMT time ──────────────────────────────────────
        echo "── Top 20 Files by SMT Time ──"
        echo ""
        printf "  %-55s %8s %6s %6s\n" "File" "SMT(s)" "#Q" "Avg(ms)"
        printf "  %-55s %8s %6s %6s\n" "----" "------" "--" "-------"

        grep -a "Query-stats" "$log" | grep "succeeded" \
            | sed -n 's/(\([^(]*\)\.\(fst\|fsti\)([^)]*)).*succeeded in \([0-9]*\) milliseconds.*/\1.\2 \3/p' \
            | awk '{files[$1]+=$2; counts[$1]++}
               END {
                 for(f in files) printf "%d %d %s\n", files[f], counts[f], f
               }' \
            | sort -rn \
            | head -20 \
            | awk '{printf "  %-55s %8.1f %6d %6d\n", $3, $1/1000, $2, ($2>0 ? $1/$2 : 0)}'

        echo ""

        # ── Top queries by wall time ───────────────────────────────────
        echo "── Top 20 Individual Queries (by wall time) ──"
        echo ""
        printf "  %-60s %8s %8s %6s\n" "Function" "Time(s)" "rlimit" "alloc"
        printf "  %-60s %8s %8s %6s\n" "--------" "-------" "------" "-----"

        grep -a "Query-stats" "$log" | grep "succeeded" \
            | sed -n 's/.*Query-stats (\([^)]*\)).*succeeded in \([0-9]*\) milliseconds.*rlimit \([0-9]*\) (used rlimit \([0-9.]*\)).*/\2\t\4\t\3\t\1/p' \
            | sort -rn \
            | head -20 \
            | awk -F'\t' '{printf "  %-60s %8.1f %8.1f %6d\n", $4, $1/1000, $2, $3}'

        echo ""

        # ── Top functions by aggregated SMT time ───────────────────────
        echo "── Top 20 Functions by Aggregated SMT Time (queries ≥ 5s) ──"
        echo ""
        printf "  %-60s %8s %6s %8s\n" "Function" "Total(s)" "#Q" "Avg(s)"
        printf "  %-60s %8s %6s %8s\n" "--------" "--------" "--" "------"

        grep -a "Query-stats" "$log" | grep "succeeded" \
            | sed -n 's/.*Query-stats (\([^,]*\),.*succeeded in \([0-9]*\) milliseconds.*/\2 \1/p' \
            | awk '$1 >= 5000 {funcs[$2]+=$1; count[$2]++}
               END {
                 for(f in funcs) printf "%d\t%d\t%s\n", funcs[f], count[f], f
               }' \
            | sort -rn \
            | head -20 \
            | awk -F'\t' '{printf "  %-60s %8.1f %6d %8.1f\n", $3, $1/1000, $2, $1/($2*1000)}'

        echo ""

        # ── Settings distribution ─────────────────────────────────────
        echo "── Fuel/iFuel/Rlimit Distribution (succeeded queries) ──"
        echo ""

        echo "  Max rlimit allocated:"
        grep -a "Query-stats" "$log" | grep "succeeded" \
            | grep -oP 'rlimit \K[0-9]+' \
            | sort -rn | head -1 | awk '{printf "    %d\n", $1}'

        echo "  Rlimit usage (allocated → used %):"
        grep -a "Query-stats" "$log" | grep "succeeded" \
            | sed -n 's/.*rlimit \([0-9]*\) (used rlimit \([0-9.]*\)).*/\1 \2/p' \
            | awk '{
                 if ($1 > 0) pct = $2*100/$1; else pct = 0;
                 if (pct < 10) b1++;
                 else if (pct < 25) b2++;
                 else if (pct < 50) b3++;
                 else if (pct < 75) b4++;
                 else b5++;
               }
               END {
                 total = b1+b2+b3+b4+b5;
                 printf "    <10%%:  %6d (%4.1f%%)\n", b1, (total>0?b1*100/total:0)
                 printf "    10-25%%: %5d (%4.1f%%)\n", b2, (total>0?b2*100/total:0)
                 printf "    25-50%%: %5d (%4.1f%%)\n", b3, (total>0?b3*100/total:0)
                 printf "    50-75%%: %5d (%4.1f%%)\n", b4, (total>0?b4*100/total:0)
                 printf "    >75%%:  %6d (%4.1f%%)\n", b5, (total>0?b5*100/total:0)
               }'

        echo ""
        echo "  Fuel distribution:"
        grep -a "Query-stats" "$log" | grep "succeeded" \
            | grep -oP 'fuel \K[0-9]+' \
            | sort -n | uniq -c | sort -rn | head -5 \
            | awk '{printf "    fuel %d: %d queries\n", $2, $1}'

        echo ""
        echo "  iFuel distribution:"
        grep -a "Query-stats" "$log" | grep "succeeded" \
            | grep -oP 'ifuel \K[0-9]+' \
            | sort -n | uniq -c | sort -rn | head -5 \
            | awk '{printf "    ifuel %d: %d queries\n", $2, $1}'

        echo ""

        # ── Errors ─────────────────────────────────────────────────────
        if [ "$n_errors" -gt 0 ]; then
            echo "── Verification Errors ──"
            echo ""
            grep -a "Error 19\|Error 17\|Error 66" "$log" | grep -av "warn_error" | while read -r line; do
                echo "  $line"
            done
            echo ""
        fi

        echo "================================================================"

    } > "$REPORT_FILE"

    cat "$REPORT_FILE"

    set -e
    # ── Generate CSV ───────────────────────────────────────────────────
    echo "── Writing CSV to $CSV_FILE..."
    {
        echo "file,function,query_num,result,time_ms,fuel,ifuel,rlimit_alloc,rlimit_used"
        grep -a "Query-stats" "$log" \
            | grep -aE "succeeded|failed" \
            | awk '
            match($0, /\(([^(]+)\.(fsti?)\(/, fa) &&
            match($0, /Query-stats \(([^,]+), ([0-9]+)\)/, qa) &&
            match($0, /(succeeded|failed)/, ra) &&
            match($0, /in ([0-9]+) milliseconds/, ta) &&
            match($0, /fuel ([0-9]+) and ifuel ([0-9]+) and rlimit ([0-9]+)/, sa) &&
            match($0, /used rlimit ([0-9.]+)/, ua) {
                printf "%s.%s,%s,%s,%s,%s,%s,%s,%s,%s\n",
                    fa[1], fa[2], qa[1], qa[2], ra[1], ta[1], sa[1], sa[2], sa[3], ua[1]
            }'
    } > "$CSV_FILE"

    local csv_lines
    csv_lines=$(wc -l < "$CSV_FILE")
    echo "── CSV: $((csv_lines - 1)) query records written"
}

# ── Main ───────────────────────────────────────────────────────────────

if [ -n "$REPORT_ONLY" ]; then
    generate_report "$REPORT_ONLY"
else
    build_rc=0
    run_build || build_rc=$?
    generate_report "$LOG_FILE"
    exit $build_rc
fi
