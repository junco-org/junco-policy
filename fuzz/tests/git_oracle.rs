//! Ground-truth replay: every operation the git trace policy grants must succeed against a real
//! repository. `git_policy_harness` generates and validates traces without touching git or the
//! filesystem; this test executes the granted ones through libgit2 on scratch repositories, and
//! retains the repository of any trace that failed.
//!
//! **libgit2 is plumbing.** It happily creates empty commits, silently ignores unmatched pathspecs
//! and has no `git rm` safety check, so every arm of `Scratch::execute` re-implements the porcelain
//! precondition of the command named on its [`GeneratedOperation`] variant before calling libgit2.
//! The oracle therefore rejects exactly what the command line rejects and nothing weaker; the
//! preconditions and their error strings are transcribed from observed `git` behaviour (2.55), not
//! from libgit2's.
//!
//! No git-config isolation — the `GIT_CONFIG_*` fencing an executor that spawned `git` would need —
//! is present, and none is needed: libgit2 runs no hooks, signs nothing, honours no pager or
//! editor, and every repository here is created and touched only through libgit2, with an explicit
//! signature and an explicit initial branch. No user or system configuration can change an outcome
//! here, so do not re-add the fencing.

use std::error::Error;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use git_policy_harness::{
    BYTES_PER_TRACE, DETERMINISTIC_SEED, GeneratedOperation, MAX_FILE_NUMBER, RANDOM_TRACE_COUNT,
    SEED_VARIABLE, SEEDED_TRACE_COUNT, TraceSummary, ValidatedOperation, ValidatedTrace, entropy,
    random_seed, validate_trace,
};
use git2::build::{CheckoutBuilder, TreeUpdateBuilder};
use git2::{
    Commit, DiffOptions, FileMode, Repository, RepositoryInitOptions, Signature, StashSaveOptions,
    Status,
};

/// Counters the fixed seeded stream must produce; a drift here means generation changed.
const SEEDED_SUMMARY: TraceSummary = TraceSummary {
    granted: 258,
    denied: 191,
    commits: 0,
};

/// Why libgit2 or a porcelain precondition rejected a granted operation.
type Rejection = Box<dyn Error + Send + Sync>;

/// Distinguishes scratch repositories created by the same process.
static SCRATCH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A granted operation the ground truth rejected; `repository` is retained for inspection.
#[derive(Debug)]
struct ReplayFailure {
    repository: PathBuf,
    message: String,
}

/// One seeded scratch repository.
struct Scratch {
    root: PathBuf,
    /// Mutable because `stash_save_ext` takes `&mut self`.
    repo: Repository,
}

/// The pooled path an operation acts on.
fn path_of(file: usize) -> String {
    format!("src/file{file}.txt")
}

/// The principal an operation is attributed to.
fn principal_of(agent: usize) -> String {
    format!("agent{agent}")
}

/// One operation as a failure report names it, e.g. `agent0 commit src/file0.txt at step 0`.
fn render(operation: &ValidatedOperation) -> String {
    format!(
        "{} {} {} at step {}",
        principal_of(operation.agent),
        operation.operation.as_str(),
        path_of(operation.file),
        operation.step
    )
}

/// The identity libgit2 records for `agent`; the address is unresolvable by construction.
fn signature(agent: usize) -> Result<Signature<'static>, Rejection> {
    let principal = principal_of(agent);
    Ok(Signature::now(
        &principal,
        &format!("{principal}@fuzz.invalid"),
    )?)
}

/// A repository path unique within this process (the counter) and across runs (the pid). The one
/// collision left is pid reuse against a retained failure, which `fs::create_dir` surfaces as
/// `AlreadyExists`; the path in that error is the remedy.
fn scratch_root(source: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "junco-policy-replay-{}-{}-{}",
        std::process::id(),
        SCRATCH_COUNTER.fetch_add(1, Ordering::Relaxed),
        source.replace('/', "-")
    ))
}

/// What `git add` and `git rm` die with when their pathspec matches neither the working tree nor
/// the index (exit 128).
fn unmatched(path: &str) -> Rejection {
    format!("pathspec '{path}' did not match any files").into()
}

/// What `git restore --staged`, `git checkout`, `git commit` and `git stash push` reject a pathspec
/// with when git knows nothing about it (exit 1; git decorates the pathspec, this does not).
fn unknown(path: &str) -> Rejection {
    format!("pathspec '{path}' did not match any file(s) known to git").into()
}

/// What `git commit -- <path>` exits 1 on when the path's working-tree content already matches
/// `HEAD`, where libgit2 would create an empty commit.
fn nothing_to_commit() -> Rejection {
    "nothing to commit".into()
}

impl Scratch {
    /// Creates a repository whose initial commit contains every pooled path. All of them are
    /// seeded regardless of what the trace touches; unused paths are inert.
    fn seed(root: PathBuf) -> Result<Self, Rejection> {
        // Not `create_dir_all`: a colliding scratch root must fail rather than be reused.
        fs::create_dir(&root)?;
        let repo = Repository::init_opts(
            &root,
            // Explicit, so a developer's `init.defaultBranch` cannot rename the branch.
            RepositoryInitOptions::new().initial_head("main"),
        )?;
        fs::create_dir_all(root.join("src"))?;

        let mut index = repo.index()?;
        for file in 0..MAX_FILE_NUMBER {
            let path = path_of(file);
            fs::write(root.join(&path), format!("seed line for file{file}\n"))?;
            index.add_path(Path::new(&path))?;
        }
        index.write()?;

        {
            // Scoped: `Tree` borrows `repo`, which is moved into the returned `Scratch`.
            let tree = repo.find_tree(index.write_tree()?)?;
            let seed = Signature::now("seed", "seed@fuzz.invalid")?;
            repo.commit(Some("HEAD"), &seed, &seed, "seed", &tree, &[])?;
        }

        Ok(Self { root, repo })
    }

    fn head(&self) -> Result<Commit<'_>, Rejection> {
        Ok(self.repo.head()?.peel_to_commit()?)
    }

    /// Executes one granted operation for real. Filesystem writes embed the step index so they can
    /// never coincidentally reproduce the committed blob.
    fn execute(&mut self, operation: &ValidatedOperation) -> Result<(), Rejection> {
        let path = path_of(operation.file);
        let relative = Path::new(&path);
        let absolute = self.root.join(&path);

        // Live state, read once: the three places git looks for a path.
        let in_worktree = absolute.is_file();
        let mut index = self.repo.index()?;
        let in_index = index.get_path(relative, 0).is_some();
        let in_head = {
            // Scoped to a `bool`: the `Stash` arm needs `&mut self.repo`, which no live `Commit`
            // or `Tree` borrow of the repository would allow. Arms that need the objects
            // themselves re-fetch them.
            let head = self.head()?;
            head.tree()?.get_path(relative).is_ok()
        };

        match operation.operation {
            // git tracks files, not directories, so a `git rm` of the last entry under `src/`
            // prunes the directory itself. Recreating it is what a real agent writing the file
            // would do.
            GeneratedOperation::Create => {
                if let Some(parent) = absolute.parent() {
                    fs::create_dir_all(parent)?;
                }
                let principal = principal_of(operation.agent);
                fs::write(
                    &absolute,
                    format!("created by {principal} at step {}\n", operation.step),
                )?;
            }
            GeneratedOperation::Modify => {
                let principal = principal_of(operation.agent);
                OpenOptions::new().append(true).open(&absolute)?.write_all(
                    format!("edited by {principal} at step {}\n", operation.step).as_bytes(),
                )?;
            }
            GeneratedOperation::Delete => fs::remove_file(&absolute)?,
            GeneratedOperation::Read => {
                fs::read(&absolute)?;
            }
            // `git add -- <path>`: of a present path stages its content, of an absent tracked path
            // stages its removal, of anything else dies.
            GeneratedOperation::Stage => {
                if in_worktree {
                    index.add_path(relative)?;
                } else if in_index {
                    index.remove_path(relative)?;
                } else {
                    return Err(unmatched(&path));
                }
                index.write()?;
            }
            // `git restore --staged -- <path>`: libgit2 rewrites the index entry from HEAD —
            // re-adding a `git rm`-ed entry, dropping a HEAD-absent one — and writes the index.
            GeneratedOperation::Unstage => {
                if !(in_head || in_index) {
                    return Err(unknown(&path));
                }
                let head = self.head()?;
                self.repo.reset_default(Some(head.as_object()), [&path])?;
            }
            // `git commit -q -m "step <n>" -- <path>`: a partial commit records the path's
            // working-tree content on top of HEAD, disregarding what is staged.
            GeneratedOperation::Commit => {
                if !(in_head || in_index) {
                    return Err(unknown(&path));
                }
                let head = self.head()?;
                let head_tree = head.tree()?;
                let mut update = TreeUpdateBuilder::new();
                if in_worktree {
                    update.upsert(&path, self.repo.blob_path(&absolute)?, FileMode::Blob);
                } else if in_head {
                    update.remove(&path);
                }

                let tree = update.create_updated(&self.repo, &head_tree)?;
                if tree == head_tree.id() {
                    return Err(nothing_to_commit());
                }

                let author = signature(operation.agent)?;
                self.repo.commit(
                    Some("HEAD"),
                    &author,
                    &author,
                    &format!("step {}", operation.step),
                    &self.repo.find_tree(tree)?,
                    &[&head],
                )?;

                // Only after a successful commit, as the CLI does: the real index gains the
                // working-tree state of the committed path and nothing else.
                if in_worktree {
                    index.add_path(relative)?;
                } else {
                    index.remove_path(relative)?;
                }
                index.write()?;
            }
            // `git checkout -q HEAD -- <path>`. From HEAD, not from the index: the index form
            // fails after a staged deletion, which is a modelling artifact rather than a policy
            // question. `force` implies libgit2's recreate-missing, so a deleted or `git rm`-ed
            // path is restored in both the working tree and the index.
            GeneratedOperation::Checkout => {
                if !in_head {
                    return Err(unknown(&path));
                }
                let mut checkout = CheckoutBuilder::new();
                checkout.force();
                checkout.path(&path);
                self.repo.checkout_head(Some(&mut checkout))?;
            }
            // `git stash push -q -- <path>`: libgit2's pathspec stash restores the path from HEAD
            // in the working tree and the index, as the CLI does.
            GeneratedOperation::Stash => {
                if !(in_head || in_index || in_worktree) {
                    return Ok(());
                }
                // "No local changes to save", exit 0. With a pathspec the CLI only weighs that
                // pathspec, so changes elsewhere in the repository do not make this a stash.
                if self.repo.status_file(relative)?.is_empty() {
                    return Ok(());
                }
                // Observed: `git stash push -- <path>` of a `git rm`-ed path exits 1 with
                // "pathspec ... did not match any file(s) known to git", where libgit2 would
                // stash the staged deletion.
                if !(in_index || in_worktree) {
                    return Err(unknown(&path));
                }

                let mut options = StashSaveOptions::new(signature(operation.agent)?);
                options.pathspec(&path);
                self.repo.stash_save_ext(Some(&mut options))?;
            }
            // `git diff -- <path>`, which cannot fail for any pathspec.
            GeneratedOperation::Diff => {
                let mut options = DiffOptions::new();
                options.pathspec(&path);
                self.repo.diff_index_to_workdir(None, Some(&mut options))?;
            }
            // `git log -- <path>`, which exits 0 for any pathspec — even one it has never heard
            // of. The walk asserts the history is readable; the path filter is deliberately not
            // reproduced, because filtering it out would assert nothing.
            GeneratedOperation::History => {
                let mut walk = self.repo.revwalk()?;
                walk.push_head()?;
                for commit in walk {
                    commit?;
                }
            }
            // `git rm -q -- <path>`, including git's `check_local_mod` refusals: without `-f` or
            // `--cached` it removes only a path whose content matches both the index and HEAD.
            GeneratedOperation::Remove => {
                if !in_index {
                    return Err(unmatched(&path));
                }
                if in_worktree {
                    let status = self.repo.status_file(relative)?;
                    let local = status.intersects(Status::WT_MODIFIED | Status::WT_TYPECHANGE);
                    let staged = status.intersects(
                        Status::INDEX_NEW | Status::INDEX_MODIFIED | Status::INDEX_TYPECHANGE,
                    );
                    match (local, staged) {
                        (true, true) => {
                            return Err(format!(
                                "the following file has staged content different from both the file and the HEAD: {path}"
                            )
                            .into());
                        }
                        (false, true) => {
                            return Err(format!(
                                "the following file has changes staged in the index: {path}"
                            )
                            .into());
                        }
                        (true, false) => {
                            return Err(format!(
                                "the following file has local modifications: {path}"
                            )
                            .into());
                        }
                        (false, false) => {}
                    }
                }

                index.remove_path(relative)?;
                index.write()?;
                if in_worktree {
                    fs::remove_file(&absolute)?;
                }
            }
            // `git clean -fq -- <path>`: tracked or absent paths are never touched, and the CLI
            // exits 0 for any pathspec.
            GeneratedOperation::Clean => {
                if !in_index && in_worktree {
                    fs::remove_file(&absolute)?;
                }
            }
        }

        Ok(())
    }
}

/// Seeds a scratch repository at `root` and replays `operations` in order, recording what ran and
/// what was in flight when a rejection stopped it.
fn replay(
    root: &Path,
    operations: &[ValidatedOperation],
    executed: &mut Vec<ValidatedOperation>,
    offending: &mut Option<ValidatedOperation>,
) -> Result<(), Rejection> {
    let mut scratch = Scratch::seed(root.to_path_buf())?;
    for operation in operations {
        *offending = Some(*operation);
        scratch.execute(operation)?;
        *offending = None;
        executed.push(*operation);
    }
    Ok(())
}

/// Replays one trace against a fresh repository, which is discarded on success and — because the
/// repository is the finding — retained on failure.
fn execute_trace(
    source: &str,
    operations: &[ValidatedOperation],
    reproduce: &str,
) -> Result<(), ReplayFailure> {
    let root = scratch_root(source);
    let mut executed = Vec::with_capacity(operations.len());
    let mut offending = None;

    let error = match replay(&root, operations, &mut executed, &mut offending) {
        Ok(()) => {
            // An undeletable scratch directory is an environment fault, not a policy finding.
            fs::remove_dir_all(&root)
                .unwrap_or_else(|error| panic!("discard {}: {error}", root.display()));
            return Ok(());
        }
        Err(error) => error,
    };

    let history: String = executed
        .iter()
        .map(|operation| format!("  {}\n", render(operation)))
        .collect();
    let offending = offending.map_or_else(
        || "repository seeding".to_owned(),
        |operation| render(&operation),
    );
    let message = format!(
        "the git policy granted an operation that git2 rejected\n\
         source: {source}\n\
         reproduce with: {reproduce}\n\
         repository (retained): {}\n\
         granted history ({} operations):\n\
         {history}\
         offending step: {offending}\n\
         error: {error}",
        root.display(),
        executed.len(),
    );

    Err(ReplayFailure {
        repository: root,
        message,
    })
}

#[test]
fn every_operation_the_git_policy_grants_succeeds_through_git2() {
    let mut traces: Vec<(String, ValidatedTrace)> =
        Vec::with_capacity(SEEDED_TRACE_COUNT + RANDOM_TRACE_COUNT);

    let mut seeded_summary = TraceSummary::default();
    for (index, bytes) in entropy(DETERMINISTIC_SEED, SEEDED_TRACE_COUNT * BYTES_PER_TRACE)
        .chunks(BYTES_PER_TRACE)
        .enumerate()
    {
        let trace = validate_trace(bytes);
        seeded_summary.granted += trace.summary.granted;
        seeded_summary.denied += trace.summary.denied;
        seeded_summary.commits += trace.summary.commits;
        traces.push((format!("seed/{index}"), trace));
    }
    assert_eq!(seeded_summary, SEEDED_SUMMARY);

    let seed = random_seed();
    for (index, bytes) in entropy(seed, RANDOM_TRACE_COUNT * BYTES_PER_TRACE)
        .chunks(BYTES_PER_TRACE)
        .enumerate()
    {
        traces.push((format!("random/{index}"), validate_trace(bytes)));
    }

    // The randomized traces differ every run, so a failure is only actionable with the seed that
    // produced them; the fixed set reproduces from its own name.
    let reproduce = format!(
        "{SEED_VARIABLE}={seed:#018x} cargo test --release --manifest-path fuzz/Cargo.toml --test git_oracle"
    );
    for (source, trace) in &traces {
        if let Err(failure) = execute_trace(source, &trace.operations, &reproduce) {
            panic!("{}", failure.message);
        }
    }

    println!(
        "replayed {} validated traces ({SEEDED_TRACE_COUNT} seeded + {RANDOM_TRACE_COUNT} random, seed {seed:#018x})",
        traces.len()
    );
}

#[test]
fn a_git_rejection_fails_the_trace_and_retains_its_repository() {
    // Committing a path with no working-tree change: libgit2 would happily create the empty
    // commit; the porcelain check must refuse it, as `git commit -- <path>` does with exit 1.
    let probe = [ValidatedOperation {
        agent: 0,
        operation: GeneratedOperation::Commit,
        file: 0,
        step: 0,
    }];

    let failure = execute_trace(
        "probe/commit-without-changes",
        &probe,
        "this probe is synthetic and takes no seed",
    )
    .expect_err("committing an unchanged path must be rejected");

    assert!(
        failure
            .message
            .contains("offending step: agent0 commit src/file0.txt at step 0"),
        "{}",
        failure.message
    );
    assert!(
        failure.message.contains("error: nothing to commit"),
        "{}",
        failure.message
    );
    assert!(
        failure.repository.is_dir(),
        "the failing repository must be retained"
    );

    // An intentional probe, not a fuzz finding: this repository is not worth keeping.
    fs::remove_dir_all(&failure.repository).expect("discard the probe repository");
}
