---
description: Add a citation to the imprimatur paper. Given a paper URL (arXiv, ACM, IEEE, etc.) or a paper title, download the PDF to Papers/, add a BibTeX entry (with url field, preferring the published version over arXiv) to about/imprimatur-paper.bib, and add one terse accurate sentence where the paper discusses that work. Self-reflect at the end and self-edit this SKILL.md if a generalizable failure mode was discovered.
allowed-tools: Bash, Read, Edit, Write, WebFetch, WebSearch
---

## Inputs

The user supplies either:
- A **URL** to a paper (arXiv abs page, ACM DL, IEEE, OpenReview, publisher PDF, etc.), or
- A **title** (possibly with author/year hints). In that case, resolve it first — see "Resolve a title".

## Repo facts (verified 2026-10-24; re-check if stale)

- PDFs go in `Papers/` at repo root. It is ignored by git (`.gitignore`): this repo is public, and third-party PDFs are not ours to redistribute. Create it if missing.
- The paper: `about/imprimatur-paper.tex` (PACMPL, `acmart`, `acmsmall`), built with imprimatur. Its references are in `about/imprimatur-paper.bib`, typeset with `\bibliographystyle{ACM-Reference-Format}` by BibTeX (latexmk runs it). The bib's top comment asks for a `url` field on every entry — honour it. Existing keys: `Pollack98`, `Wiedijk12` (first author's surname + two-digit year); `\cite{…}` gives numeric citations.
- There is a `\section{Related work}\label{sec:related}`, the last section before the bibliography (after The trusted base). Put new citations there by default, grouped with related entries. Some citations also sit in the body where the topic comes up (`Knuth84` in the Introduction; `Pollack98`/`Wiedijk12` in `\section{Rendering is faithful}`); cite in the body as well only when the point is needed there.
- Do not touch `examples/**` papers, `docs/`, or the shipped skills in `skills/` — only `about/imprimatur-paper.tex`.

If those locations have moved, locate them with `grep -n 'bibliography\|\\section' about/imprimatur-paper.tex` and `find . -name '*.bib' -not -path './.lake/*' -not -path './e2e-out/*'`, then update this SKILL.md at the end (see "Self-reflect").

## Procedure

### 1. Resolve a title (only if no URL given)

Try in order, stopping at first hit:
1. **DBLP JSON API**: `curl -s "https://dblp.org/search/publ/api?q=<urlencoded-title>&format=json&h=5"` — parse `result.hits.hit[].info` for `{title, authors, year, venue, ee, url}`. `ee` is usually the canonical paper URL.
   As of 2026-10-24 DBLP serves curl an Anubis bot-challenge HTML page instead of JSON; skip straight to Crossref, don't retry.
2. **Crossref search**: `curl -s "https://api.crossref.org/works?query.bibliographic=<title+author+venue>&rows=4"` — `message.items[]` gives `DOI`, `title`, `container-title`, `volume`, `issue`, `page`, `issued`, `author`. Good for journal papers of any age.
3. **arXiv API**: `curl -s "http://export.arxiv.org/api/query?search_query=ti:<urlencoded-title>&max_results=5"` — parse Atom XML for `<entry>` with closest title match.
4. **WebSearch tool** as last resort (Google Scholar blocks scraping; do not curl it).

Show the user the top match(es) before proceeding if there is any ambiguity. **Always prefer the published version over arXiv** when both exist — use the published venue's title, authors, year, and venue as the *primary* bibliographic data (see step 3), and treat arXiv as a secondary preprint pointer. Many papers are renamed between the arXiv preprint and the published version; the published title wins.

### 2. Download the PDF

- Filename: prefer the existing convention in `Papers/` — short, human-readable, e.g. `firstauthor-year-keyword.pdf` (lowercase, hyphens). If the paper is on arXiv, `arxiv-<id>-<keyword>.pdf` is fine. Check `ls Papers/` to mimic the dominant pattern.
- arXiv: PDF is at `https://arxiv.org/pdf/<id>` (e.g. `https://arxiv.org/pdf/2503.18813`).
- Use `curl -L -o "Papers/<filename>.pdf" "<pdf-url>"` then verify with `file Papers/<filename>.pdf` — must report `PDF document`. If it returns HTML, the publisher requires a different fetch (auth wall, JS) — tell the user and ask for a direct PDF link.
- Skip download (and tell the user) if the file already exists.

### 3. Add the BibTeX entry

- **The published version is primary.** If the paper has a published (POPL, ITP, CPP, journal, etc.) version, use its title, authors, year, and venue as the canonical entry; record the arXiv preprint only as a secondary pointer (a `note` and/or `eprint`). Use the arXiv-only form *only* when there is no published version.
- Key: first author's surname + two-digit year, matching `Pollack98`, `Wiedijk12`. Check `grep -n '^@' about/imprimatur-paper.bib` for collisions; disambiguate with a trailing letter (`Smith20a`).
- Construct the entry, mirroring the existing ones:
  - For published venues (preferred): `@inproceedings`, `@article` or `@incollection` with the published `title`, `booktitle`/`journal`, `year`, `pages` and `volume` (if known), `doi`, `url`, and a `note` recording the arXiv preprint id when there is one.
  - For arXiv-only papers: `@article` with `eprint`, `archivePrefix={arXiv}`, `primaryClass`, `url`.
- **Always** include a `url` field. Prefer a DOI link (`https://doi.org/<doi>`) over an author-hosted or publisher PDF link; a raw `*.pdf` URL is acceptable **only** when the work genuinely has no DOI (e.g. a PhD thesis or a personal-page manuscript). When no DOI is available but the paper is on arXiv, the arXiv **abstract** URL (`/abs/…`, never `/pdf/…`) is acceptable.
- **Never write a DOI, URL, or any other bibliographic detail (editors, pages, report numbers) from memory or by inference.** DOIs are not guessable and a wrong DOI is worse than none. Take each field only from a source you actually fetched this run, and verify a DOI resolves to the matching title/authors/year *before* writing it — e.g. `curl -sL https://api.crossref.org/works/<doi>` (returns JSON `title`/`author`/`issued`/`page`/`editor`), or by resolving `https://doi.org/<doi>`. If you cannot verify a field, leave it out and say so.
- **`note` is a printed field** under ACM-Reference-Format. Put only short *bibliographic* remarks there (the arXiv-preprint pointer, publication history). Prose "what this paper does" summaries go in `annote`, which the style does **not** print.
- Append to the end of `about/imprimatur-paper.bib`. Do not re-sort the file.

### 4. Write the sentence that cites it

- Read the paper enough to be accurate. For arXiv abs pages, the abstract is sufficient for one sentence; if you have the PDF, skim the intro/conclusion. **Do not** fabricate claims — if you cannot summarise from what you read, say so and stop.
- One sentence, terse, factual, in the paper's voice (declarative, present tense, plain words, no marketing adjectives). End with the cite: `~\cite{<Key>}`.
- Pick the place by topic: by default the Related work section, next to the entries the work is closest to. If genuinely uncertain, ask the user. Ask before adding a `\subsection` or `\paragraph` grouping to Related work — don't invent one silently.
- Insert at the end of the chosen paragraph or section (before the next `\section`/`\subsection`), preserving the surrounding blank lines. Do not edit generated text (theorem statements spliced by imprimatur, or anything inside `\leancheck` arguments) — `imprimatur check` would flag or overwrite it.

### 5. Report

Print a concise summary:
- PDF path
- BibTeX key
- Section the sentence was added to
- The sentence itself

### 6. Self-reflect (mandatory)

Briefly evaluate:
- Did the PDF download succeed and `file` confirm it's a PDF?
- Was the BibTeX entry well-formed and the key collision-free?
- Was the section choice obviously right, or did you guess?
- Did anything in the procedure above turn out to be inaccurate (paths moved, conventions changed, an API returned an unexpected shape)?

If any **generalisable** failure or friction was found (not specific to this one paper), edit this SKILL.md to fix it: add the gotcha, correct stale facts, or tighten an ambiguous step. Use the Edit tool. Do **not** edit for one-off quirks. Mention the edit in your final report so the user can review.

If everything worked first try, say so — no edit needed.

## Gotchas (learned)

- The `file` command is not installed in this environment. Verify PDFs with magic bytes instead: `python3 -c "print(open('Papers/x.pdf','rb').read(8))"` — must start with `%PDF`.
- The user sometimes already has the PDF locally (e.g. `~/Downloads/`) instead of giving a URL/title. Skip step 2's download — `cp` the file into `Papers/` under the usual naming convention, verify magic bytes, and confirm title/authors/venue by reading page 1 with `pdftotext -f 1 -l 1` before trusting the source filename (downloaded filenames are often mangled, e.g. a hashed suffix). If no DOI exists (common for NDSS-era proceedings), the publisher/venue's own paper page is an acceptable `url`, same as the author-homepage fallback.
- ACM DL (`dl.acm.org/doi/pdf/...`) and OUP (`academic.oup.com`, Cloudflare — even direct `article-pdf/...` URLs) serve an HTML bot-wall to curl, and author homepages may 404. For paywalled classics with no OA copy (check Semantic Scholar `openAccessPdf` and Unpaywall `api.unpaywall.org/v2/<doi>?email=...` — use a generic address such as `add-citation@example.org`, never the user's own email: it is not theirs to hand to a third-party service unless they say so), add the bib entry anyway and tell the user to fetch the PDF manually via institutional access. Fallback order: author/project site (e.g. cakeml.org for CakeML papers) → arXiv preprint PDF. If only the preprint PDF could be fetched for a published paper, keep the published version as the primary entry and note the discrepancy in the report.
- arXiv URLs come in many shapes: `/abs/XXXX.YYYYY`, `/abs/XXXX.YYYYYvN`, `/pdf/...`. Strip version suffix for the citation key but keep it in the `url` if the user gave a versioned link.
- Some `Papers/` files have `:Zone.Identifier` siblings (WSL artefacts) — ignore them.
- Pre-2000 papers on author pages (e.g. `cl.cam.ac.uk/~jrh13/papers/`) are often `.ps.gz`, and this environment has no ghostscript/ps2pdf (and no sudo). Save the gunzipped `.ps` into `Papers/` with the usual naming (`.ps` extension) and tell the user how to convert (`ps2pdf` elsewhere, or install ghostscript). Old IFIP/North-Holland proceedings typically have no DOI — an author-hosted paper page URL is acceptable.
- Do not run `lake build`, `imprimatur check`, `scripts/test-all.sh` or any TeX build as part of this skill — it's the user's call.
- On the user's WSL machine (seen from the llmbda checkout, 2026-07-09) outbound network is partially restricted: many university hosts fail (`No route to host` on wharton.upenn.edu, empty responses from buffalo.edu/washington.edu/core.ac.uk), while arxiv.org, web.archive.org, api.crossref.org, api.openalex.org, and api.semanticscholar.org work. The **Wayback Machine** is the reliable fallback for author-hosted PDFs: `https://web.archive.org/web/<year>id_/<original-url>` (the `id_` suffix returns the original bytes, not a rewritten page).
- `export.arxiv.org` (the metadata API, plain-HTTP) can return empty from restricted networks even when `arxiv.org/pdf/<id>` works. Fallback: download the PDF and read title/authors/date off page 1 with `pdftotext -l 1`.
- Verify every fetched PDF is the *right paper*, not just a PDF — mirrors and guessed arXiv ids can serve a valid PDF of something else entirely. Scanned pre-digital papers may have no text layer (`pdftotext` outputs nothing); render page 1 with `pdftoppm -png` and eyeball it.
- **ACM Queue articles**: the Queue-issue DOI may 404 at doi.org/Crossref even though DBLP lists it (seen with 10.1145/3762990); Queue articles are typically republished in CACM a few months later with a *different, registered* DOI and page numbers — search DBLP by title to find the CACM record and cite that as primary (Queue original in `note`). queue.acm.org bot-walls curl like dl.acm.org, and CACM's CC-BY PDFs on dl.acm.org are still unfetchable (Wayback `id_` often has no snapshot) — expect to hand the PDF fetch to the user.
- **Old conference abstracts in large scanned proceedings** (e.g. Indian Science Congress, 1940s): the Digital Library of India copies on archive.org (`in.ernet.dli.2015.*`, found via `archive.org/advancedsearch.php?q=title:(...)&output=json`) often bind several Parts into one volume. The plain `.pdf` is image-only; fetch the `_djvu.txt` to confirm the abstract is there, then the `_text.pdf` (OCR layer) to locate the page with `pdftotext -f N -l N`, and save only the relevant pages (`pdfseparate` + `pdfunite`) rather than the whole ~80MB volume. Use the archive.org `details/` page as the `url`.
- **Books** (esp. pre-digital): DBLP may list only the associated PhD thesis, and Crossref/OpenAlex often lack pre-~2000 CUP/Springer books entirely (probing a plausible `10.1017/CBO…` DOI can resolve to a *different* book — never guess). Resolve via OpenLibrary instead: `https://openlibrary.org/search.json?q=<title+author>` for ISBN/year, then `curl -sL https://openlibrary.org/isbn/<isbn>.json` (needs `-L`, it redirects) for publisher/series/pages. If the publisher's catalogue page is bot-walled (cambridge.org 403s curl) and there is no DOI, an author-hosted PDF or the OpenLibrary edition URL (`https://openlibrary.org/books/OL…M`) is an acceptable `url` — and ask the user, who may know an author link (microsoft.com/en-us/research hosts Gordon's).
- ScienceDirect (`sciencedirect.com/.../pdf`, including Elsevier open-archive ENTCS) returns an HTML page to curl even with a browser user agent. Use another of Unpaywall's `oa_locations`, e.g. an institutional repository handle (`hdl.handle.net/2066/…` → Radboud's `repository.ubn.ru.nl/bitstream/…pdf`): fetch the handle page and take the `bitstream` PDF link from it.
- ACM-Reference-Format lowercases `edition` and appends "ed." ("isabelle2026 ed."). Brace the value to keep its case: `edition = {{Isabelle2026}}`. It accepts `@software` (as an artifact) and `@manual`; a `@manual` with no `year` prints "n.d.", so find the release date (e.g. the GitHub releases API) rather than leave it out.
