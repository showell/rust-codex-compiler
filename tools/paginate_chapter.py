#!/usr/bin/env python3
"""Number the pages of a chapter that spans several files.

    paginate_chapter.py <file1.codex> <file2.codex> ...

The files are the pages, IN ORDER. Each gets `Page N of M` at its foot, which is
what CDX3004 requires:

    A chapter that appears once needs nothing. A chapter that appears k > 1
    times must have, on every page, `Page N of M` with M == k and the N
    distinct.  -- Syntax/Parser.codex

A single-file chapter carries a bare `Page 1` instead, and 1192 files here do.
So a marker is REPLACED, never appended: appending to ZigEmitter's existing
`Page 1` left it claiming two page numbers at once. Pass one file to put a
chapter back to the bare form.

It refuses unless every file declares the SAME chapter name, because numbering
pages of chapters that are not the same chapter is how an accidental duplicate
name becomes a silent merge -- the thing the marker exists to prevent.
"""
import pathlib, re, sys

MARKER = re.compile(r'\n+Page \d+( of \d+)?\n*\Z')
CHAPTER = re.compile(r'^Chapter:[ \t]*(.+?)[ \t]*$', re.M)

def main(paths):
    files = [pathlib.Path(p) for p in paths]
    names = []
    for f in files:
        m = CHAPTER.search(f.read_text())
        if not m:
            sys.exit(f"refusing: {f} declares no Chapter:")
        names.append(m.group(1))
    if len(set(names)) != 1:
        sys.exit("refusing: these are not one chapter -- " +
                 ", ".join(f"{f.name}={n}" for f, n in zip(files, names)))
    m = len(files)
    for n, f in enumerate(files, 1):
        body = MARKER.sub('', f.read_text()).rstrip('\n')
        marker = 'Page 1' if m == 1 else f'Page {n} of {m}'
        f.write_text(body + f'\n\n{marker}\n')
        print(f"  {marker:14} {f}")
    print(f"chapter '{names[0]}' paginated across {m} file(s)")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(sys.argv[1:])
