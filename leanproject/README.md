# CooksTheorem

A Lean 4 + mathlib project. This README documents exactly how the project
was set up on this machine, including the workarounds needed to make the
nix-provided Lean toolchain cooperate with mathlib and the VS Code Lean 4
extension.

## Environment

This machine has Lean tooling installed two different ways:

1. **nix-store `lean4` package** at
   `/nix/store/4gr3n4nrp0xxgykyyzdxi3xjj2ikn5x1-lean4-4.25.0/bin/`,
   which puts `lean`, `lake`, etc. on `$PATH` system-wide.
2. **nix-store `elan` package** at
   `/nix/store/38rp778v5gfs87nfkcvn4mafipkdbkd4-elan-4.1.2/bin/`,
   which provides the `elan` CLI but does **not** populate `~/.elan/bin`
   with shims the way the upstream `elan-init` installer would.

The system `lake` is therefore version `5.0.0-src+v4.25.0` (from Lean
4.25.0), and there are no shims in `~/.elan/bin`. This is the source of
all the trouble below.

## The Problem

Running `lake init CooksTheorem math` succeeds at the project-scaffolding
step but the post-init `lake update` fetches mathlib `master`, which has
moved past Lean 4.25.0 and uses newer Lake APIs (`Lake.Package.baseName`,
`String.trimAscii`, `dropPrefix`, ...). The system Lake 4.25.0 cannot parse
mathlib master's `lakefile.lean` and fails with:

```
error: .../mathlib/lakefile.lean:143:5:
  Invalid field `baseName`: The environment does not contain `Lake.Package.baseName`
error: .../mathlib/lakefile.lean: package configuration has errors
```

The VS Code Lean 4 extension hits the *same* error because it spawns
`lake setup-file` using whichever `lake` it finds first on `$PATH` —
which on this system is the nix-store 4.25.0 one. The extension's normal
fallback is to prepend `~/.elan/bin` to `$PATH` so its `lake` shim
dispatches via `elan`, but that directory does not exist on this nix
install, so the fallback is a no-op.

We tried several layers of indirection before giving up on them:

- `lean4.toolchainPath` in `.vscode/settings.json` — **not a real
  setting** in vscode-lean4. Has no effect.
- `lean4.envPathExtensions` pointing at the elan-managed v4.30.0-rc1
  toolchain bin directory — the documented setting, but it did not
  override the absolute lake path the extension was already using on
  this machine. (May depend on extension version, workspace trust, or
  startup ordering — we did not chase it down.)
- Hand-creating `~/.elan/bin/lake` as a symlink to the elan binary
  (the standard upstream shim layout). The shim works correctly when
  invoked manually but the VS Code extension still resolved `lake` to
  the nix-store path.

## The Fix: Pin Everything to v4.25.0

Since the system `lake` is locked at 4.25.0 and we can't realistically
shadow it for VS Code's child processes, the simplest robust fix is to
make the project itself target 4.25.0. Mathlib has a `v4.25.0` tag whose
`lakefile.lean` does **not** use any of the newer Lake APIs, so the
nix-store `lake` parses it cleanly.

### Step-by-step

From inside `/home/bepis/prog/verus-cad/lean-cooks-theorem/leanproject/`:

1. **Scaffold the project** (creates `lakefile.toml`, `lean-toolchain`,
   `CooksTheorem.lean`, `CooksTheorem/Basic.lean`):

   ```sh
   lake init CooksTheorem math
   ```

   This will produce a `lake update` failure because of the mathlib
   master / Lake 4.25.0 mismatch above. Ignore the error; the source
   files we need have already been written.

2. **Pin `lean-toolchain` to v4.25.0** (matching the nix-store lake):

   ```
   leanprover/lean4:v4.25.0
   ```

3. **Pin mathlib to the matching tag** in `lakefile.toml`:

   ```toml
   [[require]]
   name = "mathlib"
   scope = "leanprover-community"
   rev = "v4.25.0"
   ```

4. **Wipe the broken lake state** (the `master` checkout and stale
   manifest from step 1):

   ```sh
   rm -rf .lake lake-manifest.json
   ```

5. **Re-fetch dependencies** with the system lake:

   ```sh
   lake update
   ```

   `lake update` will print
   `Not running lake exe cache get yet, as the lake version does not match the toolchain version in the project.`
   That message is misleading — the version strings *do* match
   (`4.25.0`), but the post-update hook compares git commit hashes and
   the nix build of Lean 4.25.0 has a different commit hash than the
   official `leanprover/lean4:v4.25.0` release. Mathlib's
   `post_update` hook bails out, and we run cache fetching by hand in
   the next step.

6. **Fetch the prebuilt mathlib oleans** using a Lean binary whose
   commit hash matches the official 4.25.0 release. `elan` will install
   it for us:

   ```sh
   PATH=/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH \
       lake exe cache get
   ```

   This installs `leantar 0.1.16` and downloads ~7525 `.olean` files.
   The PATH override is only needed for *this one command* because
   mathlib's `Cache/IO.lean` shells out to `lean --print-prefix` and
   the nix-store `lean` does not bundle `leantar`.

7. **Build to verify**:

   ```sh
   lake build
   ```

   Expected output ends with `Build completed successfully (4 jobs).`

8. **Verify the VS Code path works**:

   ```sh
   lake setup-file CooksTheorem/Basic.lean --no-build --no-cache
   ```

   Should print a single-line JSON config with no errors. This is the
   exact command the Lean 4 extension runs when opening a file.

After this, opening the project folder in VS Code with the
**leanprover.lean4** extension installed Just Works. No `.vscode/`
configuration is required.

## Files of Interest

- `lakefile.toml` — package config; mathlib pinned to `v4.25.0`.
- `lean-toolchain` — `leanprover/lean4:v4.25.0`. Both the system
  nix-store `lake` and the elan-managed v4.25.0 toolchain match this.
- `lake-manifest.json` — committed; pins all transitive dep revisions
  to whatever `lake update` resolved against the v4.25.0 mathlib tag.
- `CooksTheorem.lean` / `CooksTheorem/Basic.lean` — entry point and
  the only place to put actual Lean code.
- `.envrc` — direnv config that prepends the elan-managed v4.25.0
  `bin/` to `PATH`. Optional; only matters if you run `lake exe cache get`
  again later, since that's the one command that needs `lean` and
  `leantar` to live in the same prefix. Run `direnv allow` once.

## Updating Mathlib

When you want a newer mathlib, do *not* simply move the `rev` to
`master`. You will hit the original Lake-API error again the moment a
mathlib commit drifts past 4.25.0. Instead:

1. Pick a newer mathlib release tag (e.g., `v4.26.0`).
2. Update `lean-toolchain` to the matching `leanprover/lean4:v4.X.Y`.
3. Update `rev` in `lakefile.toml` to the new tag.
4. `rm -rf .lake lake-manifest.json && lake update`.
5. `PATH=/home/bepis/.elan/toolchains/leanprover--lean4---v4.X.Y/bin:$PATH lake exe cache get`.
6. `lake build`.

If the new toolchain version is **not** what the system nix-store `lake`
provides (4.25.0), VS Code will go back to failing with the
`Invalid field baseName` errors because the extension still picks up
the nix-store `lake` first. To fix that you would need to either:

- update the nix `lean4` package to the new version system-wide, or
- get the Lean 4 VS Code extension to actually honor an alternate
  toolchain (the `~/.elan/bin/lake` shim approach is the intended
  upstream solution but did not work in our testing on this machine,
  see "The Problem" above).

For now, staying on `v4.25.0` is the path of least resistance.

## Why Not Use `nix develop` or a `shell.nix`?

The parent repo (`verus-cad`) already uses nix and direnv. A
project-local `shell.nix` that pulls in the right Lean version would be
the cleanest fix, but doing it correctly requires a Lean overlay and is
out of scope for "just get a Lean 4 project with mathlib working today."
The pinning approach above gives the same result with one config file
change.
