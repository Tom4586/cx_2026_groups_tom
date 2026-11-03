module

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Getting started with GitHub Codespaces

GitHub Codespaces gives you VS Code in a browser, with Lean running on a remote
computer. You need a GitHub account and an internet connection; the project
installs Lean and its dependencies for you.

## Create your codespace

1. Sign in to GitHub and open
   [the course repository](https://github.com/gihanmarasingha/cx_2026_groups).
   To keep your own exercise solutions, first use **Fork** to create a copy in
   your account, then open your fork.
2. Select the green **Code** button, then **Codespaces**, then **Create codespace
   on main** (or the branch you are using). The configuration requests a machine
   with at least four cores and 8 GB of memory.
3. Wait for setup to finish. The first start downloads the Lean version specified
   in `lean-toolchain`, fetches the precompiled Mathlib library, and builds the
   course. This can take several minutes. Leave setup running until it completes.
4. The browser opens VS Code with the Lean extension installed. This file,
   `Cx2026Groups/Week1_0.lean`, opens automatically.

## Run Lean and inspect proofs

Lean checks a file as you edit it. There is no separate Run button for a proof.
Scroll to the examples at the end of this file. Click inside the proof after
`by` and move the cursor through its lines to see the goals in **Lean Infoview**.
If that panel is hidden, open the command palette with **F1**, search for
**Lean: Toggle Infoview**, and select it.

The `#eval` command evaluates an expression; its result appears in the Infoview
when you place the cursor on that line. A theorem or `example` instead asks Lean
to check a proof. Try changing the right-hand side of the example from `4` to
`5`: Lean reports an error because the proof no longer establishes the claim.
Undo the change before continuing.

Open `Cx2026Groups/Week1_1.lean` in the Explorer to begin the rewriting exercises,
then continue with `Week1_2.lean` and `Week1_3.lean`. Replace `sorry` with your
proofs. A warning that a declaration uses `sorry` marks an unfinished exercise.

## Check the whole project

Choose **Terminal → New Terminal**. From the repository root, run:

```
lake build
```

This checks all the course modules. To check just the rewriting file, run:

```
lake env lean Cx2026Groups/Week1_1.lean
```

A successful build can still contain `sorry` warnings: it does not mean all the
exercises have been completed.

## Preview the course website

In the terminal, run:

```
lake build :literateHtml
python3 -m http.server 8000 --bind 0.0.0.0 --directory .lake/build/literate-html
```

The first website build also compiles Verso and may take a while. Open the
**Ports** tab and use **Open in Browser** for port **8000** to read the generated
notes. Keep the server running while you browse; use **Ctrl+C** in its terminal
to stop it. After editing the notes, rebuild the website and refresh the browser.

## Save your work and return later

Save files with **Ctrl+S** (or **Cmd+S** on macOS). Saving updates the codespace's
disk. To keep a copy on GitHub, open **Source Control**, stage your changes,
enter a commit message, commit, and use **Sync Changes** or **Push**. Use your
fork if you do not have write access to the course repository.

When finished, open [your codespaces](https://github.com/codespaces), find this
codespace, and choose **Stop codespace** from its menu. Resume the same codespace
next time to retain your files and installed dependencies. Codespaces uses your
account's compute and storage allowance; check GitHub's usage settings. Commit
and push work you want to keep before deleting a codespace.

## If setup or Lean fails

If the initial dependency download was interrupted, rerun
`bash .devcontainer/setup.sh` in the terminal. Read the first error if it fails
again. Once setup succeeds, open the command palette and run
**Developer: Reload Window** if the Infoview still shows missing imports.

If you created the codespace before the container configuration was added or
changed, run **Codespaces: Rebuild Container** from the command palette, then
wait for setup to finish.

For more about creating and resuming codespaces, see the
[GitHub Codespaces documentation](https://docs.github.com/en/codespaces).
-/

#eval (2 + 2 : Nat)

example : (2 : Nat) + 2 = 4 := by
  rfl
