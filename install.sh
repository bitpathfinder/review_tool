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
Usage: ./install.sh [--deps] [--dev] [--reference PATH] [--repo OWNER/NAME]
       ./install.sh --uninstall

  --deps              install the missing tools prv uses: git, python3, gh and Universal Ctags with the
                      system package manager (apt-get, dnf, zypper, pacman or brew; sudo when not root),
                      and Claude Code with its installer (https://claude.ai/install.sh)
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

deps=0 dev=0 uninstall=0 reference='' repo=''
while [ $# -gt 0 ]; do
    case $1 in
        --deps) deps=1 ;;
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

have_python() { command -v python3 >/dev/null && python3 -c 'import sys; sys.exit(sys.version_info < (3, 9))'; }
have_ctags() { case "$(ctags --version 2>/dev/null || true)" in *"Universal Ctags"*"+json"*) return 0 ;; esac; return 1; }
have_claude() { command -v claude >/dev/null || [ -x "$HOME/.local/bin/claude" ]; }

# --deps: the tools from the system package manager; Claude Code from its own installer, into $HOME.
install_deps() {
    # Words, not arrays: macOS bash 3.2 with set -u calls an empty array unbound. No package name has a space.
    local pm='' c sudo='' need='' opt='' p why=''
    for c in apt-get dnf zypper pacman brew; do
        command -v "$c" >/dev/null && { pm=$c; break; }
    done
    # pkg TOOL: the package that provides TOOL under $pm.
    pkg() {
        case $pm:$1 in
            pacman:python) echo python ;; brew:python) echo python ;; *:python) echo python3 ;;
            pacman:gh) echo github-cli ;; *:gh) echo gh ;;
            apt-get:ctags | brew:ctags) echo universal-ctags ;; *:ctags) echo ctags ;;
            *) echo "$1" ;;
        esac
    }
    command -v git >/dev/null || need="$need $(pkg git)"
    have_python || need="$need $(pkg python)"
    have_claude || command -v curl >/dev/null || opt="$opt $(pkg curl)"
    command -v gh >/dev/null || opt="$opt $(pkg gh)"
    have_ctags || opt="$opt $(pkg ctags)"
    run_pm() {
        case $pm in
            apt-get) $sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y -q "$@" ;;
            dnf) $sudo dnf install -y -q "$@" ;;
            zypper) $sudo zypper --non-interactive install "$@" ;;
            pacman) $sudo pacman -S --needed --noconfirm "$@" ;;
            brew) brew install "$@" ;;
        esac
    }
    # Claude Code needs no package manager or root. Without them, a missing git or python3 stops the install;
    # a missing gh, ctags or curl (for Claude Code), which are optional, is a warning.
    if [ -z "$pm" ]; then
        why="no apt-get, dnf, zypper, pacman or brew"
    elif [ "$pm" != brew ] && [ "$(id -u)" != 0 ]; then
        if command -v sudo >/dev/null; then sudo=sudo; else why="$pm needs root, and sudo is not installed"; fi
    fi
    if [ -n "$need$opt" ] && [ -n "$why" ]; then
        [ -z "$need" ] || die "--deps: $why; install$need yourself"
        say "warning: --deps: $why; install$opt yourself"
    elif [ -n "$need$opt" ]; then
        say "installing with $pm:$need$opt"
        [ "$pm" != apt-get ] || $sudo apt-get update -q || [ -z "$need" ] || die "apt-get update failed"
        # shellcheck disable=SC2086 # word lists
        [ -z "$need" ] || run_pm $need || die "$pm could not install$need"
        # One at a time: an older release may lack gh, which must not stop the others.
        for p in $opt; do
            run_pm "$p" || case $p in
                gh | github-cli) say "warning: $pm could not install $p; see https://github.com/cli/cli#installation" ;;
                *) say "warning: $pm could not install $p" ;;
            esac
        done
    fi
    if ! have_claude && ! command -v curl >/dev/null; then
        say "warning: --deps: no curl to install Claude Code with"
    elif ! have_claude; then
        say "installing Claude Code from https://claude.ai/install.sh"
        curl -fsSL https://claude.ai/install.sh | bash || die "the Claude Code installer failed"
    fi
}
[ -f "$SRC/prv.py" ] && [ -d "$SRC/vendor" ] || die "run install.sh from the prv checkout"
# Before --deps: a link in the way must stop the install before any package is installed.
if [ -e "$link" ] && [ ! -L "$link" ]; then
    die "$link exists and is not a link; move it away first"
fi
if [ -L "$link" ] && [[ $(readlink -- "$link") != */prv.py ]]; then
    die "$link links to $(readlink -- "$link"), not to prv; move it away first"
fi
# The config is merged at the end, and a broken one would stop the install halfway.
check_config() {
    [ -z "$reference$repo" ] || [ ! -e "$CONFIG" ] ||
        python3 -c 'import json, sys; sys.exit(not isinstance(json.load(open(sys.argv[1])), dict))' "$CONFIG" \
            2>/dev/null || die "$CONFIG is not a JSON object; fix or remove it"
}
# Before --deps too, when python3 can check it already: a broken config must not follow installed packages.
[ "$deps" = 0 ] || ! have_python || check_config
[ "$deps" = 0 ] || install_deps

# Required: python3 >= 3.9 and git.
command -v python3 >/dev/null || die "python3 is required (3.9 or newer)"
have_python ||
    die "python3 3.9 or newer is required, found $(python3 -V 2>&1)"
command -v git >/dev/null || die "git is required"
check_config

# git 2.40 added `merge-tree --merge-base`, which "Changes since..." replays the old tip with.
gitv=$(git --version | sed -n 's/^git version \([0-9]*\)\.\([0-9]*\).*/\1 \2/p')
read -r gmaj gmin <<<"${gitv:-0 0}"
if [ "$gmaj" -lt 2 ] || { [ "$gmaj" -eq 2 ] && [ "$gmin" -lt 40 ]; }; then
    say "note: git $gmaj.$gmin is older than 2.40: \"Changes since...\" shows only how each commit changed"
fi
missing=0
if ! have_claude; then
    missing=1
    say "warning: claude (Claude Code CLI) is not installed: questions, explanations and AI review will fail"
elif ! command -v claude >/dev/null; then
    say "warning: claude is in $HOME/.local/bin, which is not on PATH: prv cannot find it; add it to your shell profile"
fi
command -v gh >/dev/null || { missing=1
    say "warning: gh (GitHub CLI) is not on PATH: no GitHub comments, and \`prv new_review\` will not work"; }
have_ctags || { missing=1
    say "note: Universal Ctags with JSON output (ctags) is not installed: Ctrl-click on a name cannot jump to its definition (optional)"; }
[ "$missing" = 0 ] || [ "$deps" = 1 ] || say "./install.sh --deps installs the missing tools"
command -v qodo >/dev/null || [ -x "$HOME/.qodo/bin/qodo" ] ||
    say "note: qodo is not installed: the Qodo review button is hidden (optional, https://www.qodo.ai/)"

mkdir -p "$PRV_BIN"

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
# Logins are interactive, so they are left to the user.
if command -v gh >/dev/null && ! gh auth status >/dev/null 2>&1; then
    say "next: run \`gh auth login\` so prv can read PRs"
fi
say "done: run \`prv -h\` in a git checkout; run \`claude\` once to log in if you have not"
