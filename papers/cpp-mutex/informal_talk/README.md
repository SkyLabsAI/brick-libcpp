# C++ mutex informal talk

Start with [outline.md](outline.md): the narrative, slide claims, source coverage
table, and qualifications. [slides.md](slides.md) is the matching 37-slide
Slidev deck. It assumes basic separation logic and has no fixed time limit.
The introduction starts directly with paper code: add_two, recursive balance
transfer, shared readers/writers, and get_size with lock_guard. Highlighted
statements show the functionality without a preceding verbal overview or proof
annotations. unique_lock and scoped_lock are excluded as requested; the paper's
other program examples remain, with repeated proof figures explained later.

The source is [the supplied PDF](../.build/stdcpp.pdf). Page references use that
25-page draft. The talk preserves its anonymous attribution and does not use its
placeholder publication metadata.

The contract comparison follows §4.2.1: the unchecked Mutex1 is provable under
both the usual CSL lock contract and the paper's BRiCk C++ contract. Owner-checking
Mutex2 satisfies the latter but not the usual transferable-token contract. The
cross-thread client is admitted by the usual contract and rejected by the C++
contract. The deck keeps implementation verification and client verification
separate, and documents small repairs to the draft's schematic C++ listings.

## Run

Requires Node.js 22.12 or newer. The validated version, 22.23.3, is recorded in
[.nvmrc](.nvmrc). Node.js 18 cannot parse the regular-expression syntax used by
the installed dependencies and fails with `SyntaxError: Invalid regular
expression flags`; switch Node versions before running npm commands.

If you use nvm:

```sh
cd papers/cpp-mutex/informal_talk
nvm install
nvm use
```

With another Node version manager, select Node 22.23.3. Then install and run:

```sh
cd papers/cpp-mutex/informal_talk
node --version  # must be 22.12 or newer
npm ci
npm run dev
```

Open the address printed by Slidev (normally `http://localhost:3030`). If you
need a specific port, use `npm run dev -- --port 3031`. In a VS Code dev
container, forward that port in the **Ports** tab and use its **Open in Browser**
action.

The dev command binds to IPv4 loopback (`127.0.0.1`) so container port forwarding
can reach it. Slidev requires `--remote` for `--bind` to take effect; the explicit
loopback address keeps the server local. Without `--remote`, this environment
resolved `localhost` to IPv6 only and refused IPv4 connections. See the
[Slidev CLI options](https://sli.dev/builtin/cli).

Press `p` for presenter mode, which shows the speaker notes and timer. The deck
uses a 1280×720 stage, local fonts, and native HTML/CSS diagrams; it has no
external image assets.

```sh
npm run build     # static site in dist/
npm run export    # cpp-mutex-informal-talk.pdf
```

PDF export needs Playwright's Chromium browser and its system dependencies.
The browser package is included in the project dependencies. Generated output
and dependencies are ignored by Git.

On a fresh Linux container, install Chromium and its system libraries once:

```sh
nvm use  # if using nvm
npx playwright install --with-deps chromium
npm run export
```

The system-library installation may prompt for your sudo password. If Chromium
is already downloaded but export fails with `libnspr4.so: cannot open shared
object file` (or another missing shared library), run
`npx playwright install-deps chromium`, then retry `npm run export`. Installing
npm packages alone does not install these Linux libraries. See
[Playwright's system dependency instructions](https://playwright.dev/docs/browsers#install-system-dependencies).

Without sudo access, open the running deck's `/export` page (for example,
`http://localhost:3031/export`) in Chrome or Edge and use the
[browser exporter](https://sli.dev/guide/exporting#the-browser-exporter).

`floating-vue` is pinned to 5.2.2 for compatibility with the bundled Twoslash
integration.

## Dependency audit

The audit review on 2026-10-21 updated Slidev from 52.14.1 to 52.20.1 within the
existing major version. Targeted overrides update Monaco's DOMPurify to 3.4.17
and Mermaid's KaTeX to 0.18.10. These remove the affected DOMPurify and KaTeX
versions from the installed tree. The overrides are recorded in `package.json`,
and `package-lock.json` records the resolved dependency tree.

The remaining audit reports **17 affected packages: 11 high and 6 moderate**.
These include parent packages flagged through three underlying dependencies:

| Dependency | Dependency path and remaining fix |
| --- | --- |
| `braces@3.0.3` | Used through `fast-glob` / `micromatch` and the static-copy plugin / `chokidar`. The [advisory](https://github.com/advisories/GHSA-vfj7-8cjw-p6xm) lists no patched release. |
| `sprintf-js@1.0.3` | Used through `gray-matter` / `js-yaml` / `argparse`. The [advisory](https://github.com/advisories/GHSA-hp3w-g68c-fv3c) lists no patched release. |
| `image-size@1.2.1` | Pulled in by `pptxgenjs@4.0.1`, which requires `^1.2.1`. The [patched releases](https://github.com/advisories/GHSA-5p2g-fcmc-qvqq) start at 2.0.3, outside that dependency's supported range. |

These findings remain unresolved. Use trusted slide content and assets while
waiting for compatible upstream fixes. The audit count includes development
dependencies that build or serve the slides; excluding them from the audit
would hide the findings rather than fix them.

For future updates, use Node 22.12 or newer and run:

```sh
npm audit
npm audit fix
npm run build
```

Then check the preview and PDF export. `npm audit fix` may still return a nonzero
exit status when findings remain. At this review, `npm audit fix --force`
proposes downgrading Slidev to 51.8.2; it was not applied. The
[npm documentation](https://docs.npmjs.com/cli/v10/commands/npm-audit/)
explains that `--force` can change dependencies outside the declared ranges.

The DOMPurify and KaTeX overrides should be revisited when their parent packages
adopt patched versions. Their relevant advisories are
[DOMPurify](https://github.com/advisories/GHSA-6688-9rhm-gjv2) and
[KaTeX](https://github.com/advisories/GHSA-238p-pmpm-9mq7).

## Validation

The current 37-slide deck passed the production build and PDF export with
Slidev 53.0.0. The PDF contains 37 nonblank pages, each with its correct page
number. Browser checks of the cover, slides 9–11 (including the new BRiCk
introduction), and the final slide found no JavaScript errors, content overflow,
or page-number overlap. The PDF is available locally as
[cpp-mutex-informal-talk.pdf](cpp-mutex-informal-talk.pdf).

An earlier 36-slide version passed full-deck browser checks with Slidev 52.20.1,
including presenter notes. Its screenshots and validation report are in the
ignored `screenshots/` directory. Additional browser smoke checks at that time
exercised Mermaid rendering a mathematical label through the overridden KaTeX
version and DOMPurify 3.4.17 sanitizing HTML.

## Requested skills

The outline and deck follow the
[slide-design skill](https://github.com/hunkim/slide-skill/blob/main/SKILL.md)
and the [official Slidev skill](https://sli.dev/guide/work-with-ai#installation).
The design priority is one claim per slide with details in speaker notes.
Slidev's own project/build format takes precedence over the design skill's
generic recommendation to package an HTML deck as one standalone file.

The official installation command is:

```sh
npx skills add slidevjs/slidev
```

During preparation, the official skill was installed in an isolated temporary
tooling directory and read alongside the requested design skill. The project's
source files all live in this directory.
