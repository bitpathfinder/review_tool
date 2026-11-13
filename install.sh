#!/usr/bin/env bash
# Installs prv: copies it to $PRV_HOME and links `prv` into $PRV_BIN.
set -euo pipefail

PRV_HOME=${PRV_HOME:-"$HOME/.local/share/prv"}
PRV_BIN=${PRV_BIN:-"$HOME/.local/bin"}
# CDPATH='': with CDPATH set, cd prints the folder and SRC gets it twice.
SRC=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
CONFIG="${XDG_CONFIG_HOME:-$HOME/.config}/prv/config.json"

usage() {
    cat <<EOF
Usage: ./install.sh [--dev] [--reference PATH] [--repo OWNER/NAME]
       ./install.sh --uninstall

  --dev               link \`prv\` to this checkout instead of copying it: edits take effect at once
  --reference PATH    a local clone of the reviewed repository; \`prv new_review\` clones from it
                      with hardlinks, so a new checkout takes seconds instead of a full GitHub clone
  --repo OWNER/NAME   the GitHub repository \`prv new_review\` checks PRs out from (default scylladb/scylladb)
  --uninstall         remove the installed copy and the \`prv\` link; the config file stays

Environment: PRV_HOME (default ~/.local/share/prv), PRV_BIN (default ~/.local/bin).
--reference and --repo are saved in $CONFIG.
EOF
}

say() { printf 'install.sh: %s\n' "$*"; }
die() { say "$*" >&2; exit 1; }

dev=0 uninstall=0 reference='' repo=''
while [ $# -gt 0 ]; do
    case $1 in
        --dev) dev=1 ;;
        --uninstall) uninstall=1 ;;
        --reference) [ $# -ge 2 ] || die "--reference needs a path"; reference=$2; shift ;;
        --repo) [ $# -ge 2 ] || die "--repo needs OWNER/NAME"; repo=$2; shift ;;
        -h|--help) usage; exit 0 ;;
        *) usage >&2; exit 2 ;;
    esac
    shift
done

# Absolute: a relative link target would resolve against $PRV_BIN, not the cwd.
case $PRV_HOME in /*) ;; *) PRV_HOME=$PWD/$PRV_HOME ;; esac
case $PRV_BIN in /*) ;; *) PRV_BIN=$PWD/$PRV_BIN ;; esac
link="$PRV_BIN/prv"
# Install and uninstall replace or remove PRV_HOME/prv.py and PRV_HOME/vendor, which may be this checkout's own.
if home_real=$(cd "$PRV_HOME" 2>/dev/null && pwd -P); then
    case $SRC/ in "${home_real%/}"/*) die "PRV_HOME $PRV_HOME holds this checkout; pick another one" ;; esac
fi
# An installed copy has no install.sh or .git; another checkout or repository has its own prv.py and vendor/.
if [ -e "$PRV_HOME/install.sh" ] || [ -e "$PRV_HOME/.git" ]; then
    die "PRV_HOME $PRV_HOME is a checkout or git repository; pick another one"
fi

if [ "$uninstall" = 1 ]; then
    # Only a link to a prv.py, so another tool's `prv` stays.
    if [ -L "$link" ] && [[ $(readlink -- "$link") == */prv.py ]]; then
        rm -- "$link"
        say "removed $link"
    fi
    # Only prv's own files, so a wrong PRV_HOME never loses anything else.
    if [ -f "$PRV_HOME/prv.py" ]; then
        rm -rf -- "$PRV_HOME/prv.py" "$PRV_HOME/vendor"
        say "removed prv from $PRV_HOME"
        rmdir -- "$PRV_HOME" 2>/dev/null || say "kept $PRV_HOME: it holds other files"
    fi
    exit 0
fi

# Options first, so a bad one installs nothing.
[ -z "$reference" ] || [ -d "$reference/.git" ] || die "--reference $reference is not a git clone"
# Install replaces PRV_HOME/vendor, so PRV_HOME must be new, empty or an earlier install.
if [ "$dev" = 0 ] && [ -d "$PRV_HOME" ] && [ ! -f "$PRV_HOME/prv.py" ] && [ -n "$(ls -A -- "$PRV_HOME")" ]; then
    die "PRV_HOME $PRV_HOME holds other files; pick an empty or new folder"
fi
[ -z "$repo" ] || [[ $repo =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] || die "--repo must be OWNER/NAME"

# Required: python3 >= 3.9 and git.
command -v python3 >/dev/null || die "python3 is required (3.9 or newer)"
python3 -c 'import sys; sys.exit(sys.version_info < (3, 9))' ||
    die "python3 3.9 or newer is required, found $(python3 -V 2>&1)"
command -v git >/dev/null || die "git is required"
# Before installing: the config is merged at the end, and a broken one would stop the install halfway.
if [ -n "$reference$repo" ] && [ -e "$CONFIG" ]; then
    python3 -c 'import json, sys; sys.exit(not isinstance(json.load(open(sys.argv[1])), dict))' "$CONFIG" \
        2>/dev/null || die "$CONFIG is not a JSON object; fix or remove it"
fi

# git 2.41 added %(ahead-behind), which prv uses to guess the base branch.
gitv=$(git --version | sed -n 's/^git version \([0-9]*\)\.\([0-9]*\).*/\1 \2/p')
read -r gmaj gmin <<<"${gitv:-0 0}"
if [ "$gmaj" -lt 2 ] || { [ "$gmaj" -eq 2 ] && [ "$gmin" -lt 41 ]; }; then
    say "warning: git $gmaj.$gmin is older than 2.41: pass the base to prv yourself (prv master), it cannot guess it"
fi
command -v claude >/dev/null ||
    say "warning: claude (Claude Code CLI) is not on PATH: questions, explanations and AI review will fail"
command -v gh >/dev/null ||
    say "warning: gh (GitHub CLI) is not on PATH: no GitHub comments, and \`prv new_review\` will not work"
command -v qodo >/dev/null || [ -x "$HOME/.qodo/bin/qodo" ] ||
    say "note: qodo is not installed: the Qodo review button is hidden (optional)"

[ -f "$SRC/prv.py" ] && [ -d "$SRC/vendor" ] || die "run install.sh from the prv checkout"
mkdir -p "$PRV_BIN"
if [ -e "$link" ] && [ ! -L "$link" ]; then
    die "$link exists and is not a link; move it away first"
fi
if [ -L "$link" ] && [[ $(readlink -- "$link") != */prv.py ]]; then
    die "$link links to $(readlink -- "$link"), not to prv; move it away first"
fi

if [ "$dev" = 1 ]; then
    target="$SRC/prv.py"
else
    mkdir -p "$PRV_HOME"
    rm -rf -- "$PRV_HOME/vendor"
    cp "$SRC/prv.py" "$PRV_HOME/prv.py"
    cp -R "$SRC/vendor" "$PRV_HOME/vendor"
    target="$PRV_HOME/prv.py"
fi
chmod +x "$target"
ln -sfn "$target" "$link"
say "installed $link -> $target"

if [ -n "$reference$repo" ]; then
    mkdir -p "$(dirname "$CONFIG")"
    # Merged into an existing config, so one option does not drop the other.
    python3 - "$CONFIG" "$reference" "$repo" <<'EOF'
import json, os, sys
path, reference, repo = sys.argv[1:]
cfg = {}
if os.path.exists(path):
    with open(path) as fh:
        cfg = json.load(fh)
if reference:
    cfg["reference"] = os.path.abspath(os.path.expanduser(reference))
if repo:
    cfg["repo"] = repo
with open(path, "w") as fh:
    json.dump(cfg, fh, indent=2)
    fh.write("\n")
EOF
    say "wrote $CONFIG"
fi

"$link" --help >/dev/null || die "$link --help failed"
case ":$PATH:" in
    *":$PRV_BIN:"*) ;;
    *) say "warning: $PRV_BIN is not on PATH; add it to your shell profile" ;;
esac
say "done: run \`prv -h\` in a git checkout"
