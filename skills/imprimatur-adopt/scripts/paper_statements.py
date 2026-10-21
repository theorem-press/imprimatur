#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""List the formal statements of a LaTeX paper: every theorem-like
environment, with its number as LaTeX would print it, label, file, line and
text. Follows \\input and \\include from the main file, and reads the
environments and their numbering from \\newtheorem.

    paper_statements.py MAIN.tex [--json]

The numbering is a best effort: it handles \\newtheorem{env}{Name}[section]
and shared counters (\\newtheorem{lemma}[theorem]{Lemma}), counts
\\section and \\appendix, and ignores starred environments' numbers.
"""
import json
import os
import re
import sys


def read_tree(path, seen=None):
    """The text of a file with its \\input and \\include expanded, as a list
    of (file, line number, line)."""
    seen = seen or set()
    path = os.path.normpath(path)
    if not path.endswith(".tex") and not os.path.exists(path):
        path += ".tex"
    if path in seen or not os.path.exists(path):
        return []
    seen.add(path)
    out = []
    base = os.path.dirname(path)
    for n, line in enumerate(open(path, encoding="utf-8", errors="replace"), 1):
        code = re.sub(r"(?<!\\)%.*", "", line)
        m = re.search(r"\\(?:input|include)\{([^}]*)\}", code)
        if m:
            out.extend(read_tree(os.path.join(base, m.group(1)), seen))
        else:
            out.append((path, n, line))
    return out


def main():
    main_tex = sys.argv[1]
    as_json = "--json" in sys.argv
    lines = read_tree(main_tex)
    text = "".join(l for _, _, l in lines)
    # Environments: env -> (printed name, counter, reset-by)
    envs = {}
    for m in re.finditer(r"\\newtheorem\*?\{(\w+)\}(?:\[(\w+)\])?\{([^}]*)\}(?:\[(\w+)\])?", text):
        env, shared, name, within = m.groups()
        envs[env] = (name, shared or env, within)
    counters = {}
    section, appendix = 0, False
    results = []
    i = 0
    while i < len(lines):
        f, n, line = lines[i]
        code = re.sub(r"(?<!\\)%.*", "", line)
        if re.search(r"\\appendix\b", code):
            appendix, section = True, 0
        if re.search(r"\\section\*?\{", code) and not re.search(r"\\section\*", code):
            section += 1
            counters = {k: v for k, v in counters.items() if envs.get(k, ("", k, None))[2] != "section"}
            for env, (_, ctr, within) in envs.items():
                if within == "section":
                    counters[ctr] = 0
        m = re.search(r"\\begin\{(\w+)(\*?)\}(\[[^\]]*\])?", code)
        if m and m.group(1) in envs:
            env, star, title = m.group(1), m.group(2), m.group(3)
            name, ctr, within = envs[env]
            number = None
            if not star:
                counters[ctr] = counters.get(ctr, 0) + 1
                sec = chr(ord("A") + section - 1) if appendix else str(section)
                number = f"{sec}.{counters[ctr]}" if within == "section" or envs.get(ctr, ("", "", None))[2] == "section" else str(counters[ctr])
            # The body, to the matching \end.
            body, j = [], i
            while j < len(lines):
                body.append(lines[j][2])
                if re.search(r"\\end\{" + re.escape(env) + r"\*?\}", lines[j][2]):
                    break
                j += 1
            body_text = "".join(body)
            label = re.search(r"\\label\{([^}]*)\}", body_text)
            results.append({"env": env, "name": name, "number": number,
                            "title": title.strip("[]") if title else None,
                            "label": label.group(1) if label else None,
                            "file": os.path.relpath(f, os.path.dirname(main_tex) or "."),
                            "line": n, "text": body_text.strip()})
            i = j
        i += 1
    if as_json:
        json.dump(results, sys.stdout, indent=1, ensure_ascii=False)
        print()
    else:
        for r in results:
            head = f"{r['name']} {r['number'] or ''}".strip()
            title = f" ({r['title']})" if r["title"] else ""
            print(f"{head}{title}  [{r['label'] or '-'}]  {r['file']}:{r['line']}")
        print(f"{len(results)} statements")


if __name__ == "__main__":
    main()
