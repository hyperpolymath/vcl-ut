<!--
  CROSS-SESSION HANDOFF NOTE — from the Claude session that rebased PR #21.
  This file is an UNTRACKED scratch message for the Claude actively working
  this worktree. It is NOT source. Do NOT `git add`/commit it; delete it
  once read. It does not modify any tracked file or git state.
-->

# vcl-ut PR #21 — cross-session note (2026-05-19)

**To: the Claude actively working `_wt-vclut-phase1` (Phase 2 de-vacuization).**
**From: the session that rebased #21 onto post-#20 main and gated it.**

## What I did (and why your worktree looked the way it did)
- `#20` is **MERGED** to `main` (`89c64a1`).
- I rebased #21 onto post-#20 main: `git rebase --onto origin/main 81f8e33`
  → tip `25a3296`. This is the foundation **you built Phase 2 on top of**
  (`25a3296` ← `51831b5` L5 ← `79d1ef3` L2 + your current WIP). Your adoption
  of it is correct; nothing of yours was lost.
- I proved via a local **real-file** idris2-0.8.0 corpus build (reconstructs
  the symlink tree as real files, bypassing this WSL clone's
  `core.symlinks=false` confound — naive local builds here are unreliable;
  use this technique) that `25a3296` does **not** compile: the old
  `Composition.joinWhereTypeSafe` referenced `NoWhere`/`WhereTypeSafe`,
  which #20 removed when it redefined L2 `AllComparisonsTypeSafe` to
  `MkAllCompat : whereComparisonsCompatible m schema = True -> …`.
  You have since fixed exactly this (`whereCompatJoin`/`MkAllCompat`). Good.
- I converted PR #21 to **DRAFT** and posted two close-out comments
  (latest: issue-comment-4483359972) so it cannot be admin-merged broken.
  The remote PR head is still the stale, non-compiling `25a3296`.

## The decision is YOURS to make
The user wants you to decide #21's disposition. Key facts for that call:

1. **Remote `25a3296` is stale & broken.** Your Phase-2 fixes (`51831b5`,
   `79d1ef3`, + uncommitted `Checker/Composition/Decide/Levels.idr`) are
   **local-only, unpushed**. Until you push, the PR cannot be made ready.
2. **Merge oracle = the idris2 build, never GitHub-MERGEABLE.** Before
   un-drafting/merging, get the real-file local build (or the
   `idris2 0.8.0 --build vclut-core` CI job) green. Do not admin-merge a
   proof corpus past a non-green build — that is the antipattern this whole
   PR exists to kill.
3. **No proof escapes** (`believe_me`/`assert_*`/`postulate`/`sorry`/
   `idris_crash`/`Obj.magic`) — rhodibot CI greps & bans them.
4. **Backup** of the original pre-rebase #21 tip: local ref
   `backup/vclut-21-prerebase-3a4ec43` (compiled green, but pre-#20,
   7-module). Don't resurrect it; it's a safety net only.

## Suggested path (you decide)
Finish Phase 2 → run the **real-file local idris2 build** to green →
commit → push the branch → mark PR #21 **ready** → let CI confirm →
then it can land. Refs standards#124 (does **not** Close — the user
closes the epic). Update the shared memory
(`project_vclut_hole_deeper_than_documented.md`) when state changes;
its top "📌 CLOSE-OUT CONSOLIDATED STATE" block is the current handoff.

— Delete this file once you've read it.
