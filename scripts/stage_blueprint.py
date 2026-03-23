#!/usr/bin/env python3
"""Stage LeanArchitect-generated blueprint files flat into blueprint/src/.

LeanArchitect generates module header files and artifact files with absolute
paths in a nested directory structure under .lake/build/blueprint/module/. On
github CI, plastex (run by `leanblueprint web` from blueprint/src/) can only
resolve input paths that are plain filenames in the same directory -- it cannot
navigate into subdirectories.

This script copies everything flat into blueprint/src/:
  - Library index  -> blueprint/src/Graphs.tex   (with lm_*/la_* refs)
  - Module headers -> blueprint/src/lm_Graphs.tex, lm_Graphs_Separation.tex, ...
  - Artifact files -> blueprint/src/la_Graphs_def_foo.tex, ...
"""
import os
import re
import shutil
import sys


def find_modpath(path: str) -> str | None:
    """Return the absolute path up to and including the 'module' component."""
    parts = path.replace("\\", "/").split("/")
    for i, part in enumerate(parts):
        if part == "module":
            return "/".join(parts[: i + 1])
    return None


def mod_flat(modpath: str, abs_path: str) -> str:
    """Flat filename stem for a module header (no subdirectory).

    Examples:
      {modpath}/Graphs.tex           -> lm_Graphs
      {modpath}/Graphs/Separation.tex -> lm_Graphs_Separation
    """
    rel = abs_path[len(modpath) + 1 :].replace("\\", "/")
    rel = re.sub(r"\.tex$", "", rel)
    return "lm_" + rel.replace("/", "_")


def artif_flat(modpath: str, abs_ref: str) -> str:
    r"""Flat filename stem for an artifact reference (no subdirectory).

    The \input{} in a module header references artifact files WITHOUT .tex:
      {modpath}/Graphs.artifacts/def:foo          -> la_Graphs_def:foo
      {modpath}/Graphs/Separation.artifacts/def:bar -> la_Graphs_Separation_def:bar
    """
    rel = abs_ref[len(modpath) + 1 :].replace("\\", "/")
    rel = re.sub(r"\.tex$", "", rel)
    # Replace .artifacts/ separator
    rel = re.sub(r"\.artifacts/", "_", rel)
    rel = rel.replace("/", "_")
    return "la_" + rel


def main() -> None:
    libfile = ".lake/build/blueprint/library/Graphs.tex"
    src = "blueprint/src"

    if not os.path.exists(libfile):
        print(f"ERROR: {libfile} not found", file=sys.stderr)
        sys.exit(1)

    with open(libfile) as f:
        lib = f.read()

    mod_inputs = re.findall(r"\\input\{([^}]+)\}", lib)
    if not mod_inputs:
        print("ERROR: no \\input found in library file", file=sys.stderr)
        sys.exit(1)

    modpath = find_modpath(mod_inputs[0])
    if not modpath:
        print(f"ERROR: no 'module' component in: {mod_inputs[0]}", file=sys.stderr)
        sys.exit(1)
    print(f"Module path: {modpath}")

    if not os.path.isdir(modpath):
        print(f"ERROR: module dir not found: {modpath}", file=sys.stderr)
        sys.exit(1)

    os.makedirs(src, exist_ok=True)

    staged_modules = 0
    staged_artifacts = 0

    for mod_abs in mod_inputs:
        if not os.path.exists(mod_abs):
            print(f"WARNING: module file not found: {mod_abs}", file=sys.stderr)
            continue

        with open(mod_abs) as f:
            content = f.read()

        # Collect artifact refs (absolute paths starting with modpath)
        artif_refs = [
            m
            for m in re.findall(r"\\input\{([^}]+)\}", content)
            if m.startswith(modpath)
        ]

        # Rewrite artifact refs to flat names inside the module header
        def replace_artif(m: re.Match) -> str:
            p = m.group(1)
            if p.startswith(modpath):
                return f"\\input{{{artif_flat(modpath, p)}}}"
            return m.group(0)

        new_content = re.sub(r"\\input\{([^}]+)\}", replace_artif, content)

        # Write the (rewritten) module header flat into blueprint/src/
        flat_name = mod_flat(modpath, mod_abs)
        dst = os.path.join(src, flat_name + ".tex")
        with open(dst, "w") as f:
            f.write(new_content)
        staged_modules += 1

        # Copy artifact files flat into blueprint/src/
        for artif_abs in artif_refs:
            # LeanArchitect writes artifact files WITH .tex extension,
            # but the \input{} reference omits it.
            artif_file = artif_abs + ".tex"
            if not os.path.exists(artif_file):
                artif_file = artif_abs  # already has .tex
            if not os.path.exists(artif_file):
                print(f"WARNING: artifact file not found: {artif_abs}", file=sys.stderr)
                continue
            flat = artif_flat(modpath, artif_abs)
            dst_artif = os.path.join(src, flat + ".tex")
            shutil.copy2(artif_file, dst_artif)
            staged_artifacts += 1

    # Write the rewritten library index flat into blueprint/src/
    def replace_mod(m: re.Match) -> str:
        p = m.group(1)
        if p.startswith(modpath):
            return f"\\input{{{mod_flat(modpath, p)}}}"
        return m.group(0)

    new_lib = re.sub(r"\\input\{([^}]+)\}", replace_mod, lib)
    with open(os.path.join(src, "Graphs.tex"), "w") as f:
        f.write(new_lib)

    print(f"Staged {staged_modules} modules, {staged_artifacts} artifacts (all flat in {src}/)")


if __name__ == "__main__":
    main()
