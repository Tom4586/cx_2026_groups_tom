# Project maintenance

## Course website

The course website uses [Verso](https://verso.lean-lang.org/)'s literate
programming renderer. It turns the explanations and proofs in the course's
Lean files into readable pages with interactive proof states and hover information.
Build and preview it from the repository root:

```sh
lake build :literateHtml
python3 -m http.server 8000 --directory .lake/build/literate-html
```

Open <http://localhost:8000>. The first build compiles Verso and can take a while.
For the ordinary course library build, use `lake build`.

Write course explanations in module comments (`/-! ... -/`) alongside the Lean
code in `Cx2026Groups/`. Import each new week in `Cx2026Groups.lean` so it is
included in the course library and website. The overview in `Cx2026Groups.lean`
is the home page. Edit `literate.toml` to set page titles and navigation order;
new course modules are included automatically. Only the course library is
published, so Mathlib and Lean dependency sources are not rendered as course pages.
See the [Verso literate programming guide](https://verso.lean-lang.org/doc/latest/)
for additional rendering options.

Verso is pinned to a Lean 4.35.0-compatible backport that fixes rendering files
using `module`. 

GitHub Actions builds the library and website on pushes and pull requests.
Pushes to the default branch also publish `.lake/build/literate-html` to
GitHub Pages. Set **Settings → Pages → Build and deployment → Source** to
**GitHub Actions** when enabling Pages for the repository.

## Temporary Verso backport

The course uses Lean and Mathlib 4.35.0. Verso's official `v4.35.0` release
fails to render some files using `module`, reporting “missing data file for
module …”. Upstream [PR #1043](https://github.com/leanprover/verso/pull/1043)
fixes the import handling, but was merged after that release.

A **backport** applies a newer fix to an older software version. We use
[Taylor Dupuy's backport](https://github.com/tdupu/verso/commit/6c1b93307c6637ab5d0ae1cd9560a7e55fd6680f)
of that fix onto Verso 4.35.0. `lakefile.toml` pins the fork to this exact
commit so builds are reproducible. This is a temporary third-party dependency;
it does not automatically receive later fixes. The request for an official
4.35 backport is [issue #1052](https://github.com/leanprover/verso/issues/1052).

## Course dark-mode stylesheet

`course.css`, loaded through `extra_css` in `literate.toml`, fixes unreadable
Lean code in Verso 4.35's literate dark theme. The generated `verso-vars.css`
sets `--verso-code-color` to black; `literate.css` changes the backgrounds and
prose colours for dark mode but does not override that code colour. Keywords,
names, literals, and punctuation therefore remain black on dark backgrounds.

Our stylesheet makes `--verso-code-color` follow `--verso-text-color` only when
the browser prefers dark mode. It also applies to highlighted code in proof
states and tooltips. Light-mode colours are unchanged. This is a course-owned
stylesheet, not an edit to Verso or its backport, and it is copied into the
generated site during `lake build :literateHtml`.

After upgrading Verso, check the overview, Week 1 code, expanded proof states,
and hover tooltips in both OS light and dark modes. If the official theme now
renders code readably without the override, remove `course.css` and its
`extra_css` entry in `literate.toml`, rebuild, and check both modes again.

## Upgrading Lean and Mathlib

1. Work on a branch. Choose the desired Mathlib release and set `lean-toolchain`
   to the Lean version required by that release. Update Mathlib's `rev` in
   `lakefile.toml` accordingly.
2. Find an official Verso release or immutable revision compatible with that
   Lean version and containing PR #1043. Once available for the chosen version,
   change Verso's Git URL back to `https://github.com/leanprover/verso.git` and
   replace the backport revision. Check its `lean-toolchain`; avoid following
   `main` blindly. Remove the temporary-backport comment in `lakefile.toml`.
3. Run `lake update`, then `lake exe cache get` to fetch Mathlib's prebuilt
   artifacts. Fix any course proofs or configuration affected by upstream changes.
4. Run `lake build` and `lake build :literateHtml`. Preview
   `.lake/build/literate-html` and check the prose, navigation, and proof states.
5. Update this note and the README, commit `lean-toolchain`, `lakefile.toml`,
   `lake-manifest.json`, and any course changes, and confirm that GitHub Actions
   builds and deploys successfully.

Keep `module` in course files; the backport needs no special changes to their
content. Adapting proofs to newer Mathlib APIs is a separate part of the upgrade.
Do not edit generated files under `.lake/` or patch dependencies there: such
changes would not be reproduced in a fresh checkout or on GitHub Actions.
