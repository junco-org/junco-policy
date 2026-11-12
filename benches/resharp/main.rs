//! Criterion comparison of the junco `Validator` with RE# on RE#'s benchmark workloads; see
//! `README.md` for the workloads, their translation, and the measurement boundary.
//!
//! Run with `cargo bench --bench resharp`; filter with e.g. `-- corpus/literal-miss`.

use std::hint::black_box;
use std::sync::Arc;
use std::time::{Duration, Instant};

use criterion::{Criterion, SamplingMode, Throughput, criterion_group};
use history_semantics::Validator;
use history_store::{Checkpoint, Store};
use history_syntax::{Component3, ComponentPattern, Head, RegexExpr, Rule, RuleMode};
use junco_core::Request;
use resharp::{RegexOptions, UnicodeMode};

mod translate;

use translate::{Symbol, class, contains, literal, plain, tail, translate};

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/benches/resharp/data");

fn haystack(name: &str) -> Arc<[u8]> {
    std::fs::read(format!("{DATA}/haystacks/{name}"))
        .expect(name)
        .into()
}

fn take_lines(bytes: &[u8], n: usize) -> &[u8] {
    if n == 0 {
        return &bytes[..0];
    }
    let end = bytes
        .iter()
        .enumerate()
        .filter(|&(_, &byte)| byte == b'\n')
        .nth(n - 1)
        .map_or(bytes.len(), |(index, _)| index);
    &bytes[..end]
}

fn popular_haystack() -> Arc<[u8]> {
    let lines = [
        "2021-08-14 request Version/12.4 from https://example.com/path?q=1",
        "user_name-01 committed abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdef01",
        "apple and carrot were 42 items --- separated___by...punctuation",
        "the quick brown fox jumps over 1024 lazy dogs near https://rust-lang.org",
        "",
        "",
        "",
        "42",
        "config value = 3.14159 tag=v2 build#77 status: OK",
        "<b>Bold</b> and <br/> and <> empty tag here",
        "\x1b[31mERROR\x1b[0m: build failed at 1.2.3, retry with 1.4.0",
        "Hello ${name}, your balance is ${amount} USD",
        "run `cargo build --release` then retest the test suite again",
        "set title to \"hello world\" and note to \"a  test\"",
        "see [docs](https://example.com/docs) for  more   details",
        "<script src=\"a.js\"></script> and <SCRIPT>if (a<b) { y = 2; }</SCRIPT>",
        "column deleted_at is nullable but mut_deleted_at and deleted_at_utc are not soft-delete columns",
        "Price is 5.99 and quantity is 3. Also see 12.5kg and end.",
        "<a href=\"x\"   target=\"_blank\" class='y'   data-x=1>",
    ];
    let mut text = String::with_capacity((1 << 20) + 256);
    let mut index = 0;
    while text.len() < 1 << 20 {
        text.push_str(lines[index % lines.len()]);
        text.push('\n');
        index += 1;
    }
    text.into_bytes().into()
}

struct Workload {
    group: String,
    resharp: String,
    junco: RegexExpr<Symbol>,
    haystack: Arc<[u8]>,
}

impl Workload {
    fn standard(group: impl Into<String>, pattern: &str, haystack: Arc<[u8]>) -> Self {
        Self::custom(group, pattern, tail(translate(pattern)), haystack)
    }

    fn custom(
        group: impl Into<String>,
        resharp: &str,
        junco: RegexExpr<Symbol>,
        haystack: Arc<[u8]>,
    ) -> Self {
        Self {
            group: group.into(),
            resharp: resharp.to_owned(),
            junco,
            haystack,
        }
    }
}

fn resharp_regex(pattern: &str) -> resharp::Regex {
    resharp::Regex::with_options(
        pattern,
        RegexOptions::default()
            .unicode(UnicodeMode::Ascii)
            .multiline(false),
    )
    .expect(pattern)
}

fn candidate_head() -> Head<Symbol> {
    Head::new([
        ComponentPattern::variable("P"),
        ComponentPattern::variable("A"),
        ComponentPattern::constant(Component3::C2(Symbol::Candidate)),
    ])
}

struct Scenario {
    validator: Validator<Symbol>,
    replay: Option<(Checkpoint, Symbol)>,
}

fn seed(junco: RegexExpr<Symbol>, haystack: &[u8]) -> Scenario {
    let mut builder = Validator::builder(Arc::new(Store::new().unwrap()));
    builder
        .add_rule(Rule::new(RuleMode::Require, candidate_head(), junco))
        .expect("workload tail compiles");
    let mut validator = builder.finish().unwrap();
    let mut replay = None;
    for (index, &byte) in haystack.iter().enumerate() {
        if index + 1 == haystack.len() {
            replay = Some((validator.checkpoint(), Symbol::Byte(byte)));
        }
        assert!(
            validator
                .check(Request::new(Symbol::Byte(byte), ()))
                .unwrap()
                .is_grant()
        );
    }
    assert_eq!(validator.history().len(), haystack.len());
    Scenario { validator, replay }
}

fn bench(criterion: &mut Criterion, workload: Workload) {
    let rs = resharp_regex(&workload.resharp);
    let expected = rs.is_match(&workload.haystack).expect(&workload.group);
    let mut scenario = seed(workload.junco, &workload.haystack);
    assert_eq!(
        scenario.validator.permits(&Symbol::Candidate).unwrap(),
        expected,
        "{}",
        workload.group
    );
    let mut group = criterion.benchmark_group(&workload.group);
    group
        .sampling_mode(SamplingMode::Flat)
        .sample_size(20)
        .warm_up_time(Duration::from_millis(500))
        .measurement_time(Duration::from_secs(2))
        .throughput(Throughput::Bytes(workload.haystack.len() as u64));
    group.bench_function("junco", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut elapsed = Duration::ZERO;
            for _ in 0..iterations {
                if let Some((before_final, final_event)) = scenario.replay {
                    scenario.validator.rollback(before_final).unwrap();
                    assert!(
                        scenario
                            .validator
                            .check(Request::new(final_event, ()))
                            .unwrap()
                            .is_grant()
                    );
                }
                let start = Instant::now();
                let permitted = scenario
                    .validator
                    .permits(black_box(&Symbol::Candidate))
                    .unwrap();
                elapsed += start.elapsed();
                assert_eq!(permitted, expected);
            }
            elapsed
        });
    });
    group.bench_function("resharp", |bencher| {
        bencher.iter(|| rs.is_match(black_box(&workload.haystack)).unwrap());
    });
    group.finish();
}

fn popular_scan(criterion: &mut Criterion) {
    let haystack = popular_haystack();
    let mut workloads = Vec::new();
    for (name, pattern) in [
        ("whitespace", r"\s+"),
        ("digits", r"\d+"),
        ("dot-star", r".*"),
        ("html-tag", r"<[^>]+>"),
        ("blank-lines", r"\n{3,}"),
        ("ansi-escape", r"\x1b\[[0-9;]*m"),
        ("template-var", r"\$\{([^}]+)\}"),
        ("html-tag-any", r"<[^>]*>"),
        ("word", r"\w+"),
        ("dash-run", r"-+"),
        ("literal-test", "test"),
        ("semver", r"\d+\.\d+\.\d+"),
        ("digits-class", "[0-9]+"),
        ("code-span", "`([^`]+)`"),
        ("quoted-string", r#""([^"]+)""#),
        ("md-link", r"\[([^\]]+)\]\(([^)]+)\)"),
        ("multi-space", r"\s{2,}"),
        ("uppercase-letter", "[A-Z]"),
    ] {
        workloads.push(Workload::standard(
            format!("popular/scan/{name}"),
            pattern,
            Arc::clone(&haystack),
        ));
    }
    let not_underscore = || class((0..=255u8).filter(|b| *b != b'_'));
    for (name, pattern, junco) in [
        (
            "script-tag",
            r"(?i)<script[^>]*>~(_*</script>_*)</script>",
            contains(RegexExpr::concat([
                plain("(?i)<script[^>]*>"),
                RegexExpr::complement(contains(plain("(?i)</script>"))),
                plain("(?i)</script>"),
            ])),
        ),
        (
            "deleted-at-token",
            r"(?<!\_)deleted\_at(?!\_)",
            RegexExpr::concat([
                RegexExpr::union([
                    RegexExpr::epsilon(),
                    RegexExpr::concat([RegexExpr::all(), not_underscore()]),
                ]),
                literal(b"deleted_at"),
                RegexExpr::union([
                    RegexExpr::epsilon(),
                    RegexExpr::concat([not_underscore(), RegexExpr::all()]),
                ]),
            ]),
        ),
        (
            "decimal-point",
            r"(?<=\d)\.(?=\S)",
            contains(plain(r"\d\.\S")),
        ),
        (
            "attribute-whitespace",
            r#"(?<="|')\s+(?=[^<>\s]+=)"#,
            contains(plain(r#"["']\s+[^<>\s]+="#)),
        ),
    ] {
        workloads.push(Workload::custom(
            format!("popular/scan/{name}"),
            pattern,
            junco,
            Arc::clone(&haystack),
        ));
    }
    for workload in workloads {
        bench(criterion, workload);
    }
}

fn popular_validate(criterion: &mut Criterion) {
    let mut workloads = Vec::new();
    for (name, pattern, sample) in [
        (
            "email",
            r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$",
            "user.name+tag@example.co",
        ),
        ("iso-date", r"^\d{4}-\d{2}-\d{2}$", "2021-08-14"),
        ("empty-line", "^$", ""),
        ("numeric-line", r"^\d+$", "1234567890"),
        (
            "identifier",
            "^[a-zA-Z_][a-zA-Z0-9_]*$",
            "some_ident_name123",
        ),
        ("slug", "^[a-zA-Z0-9_-]+$", "some-slug_name-123"),
    ] {
        workloads.push(Workload::standard(
            format!("popular/validate/{name}"),
            pattern,
            Arc::from(sample.as_bytes()),
        ));
    }
    for (name, pattern, junco, sample) in [
        (
            "password-strength",
            r"^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$",
            RegexExpr::intersect([
                plain(r"[A-Za-z\d@$!%*?&]{8,}"),
                contains(plain("[a-z]")),
                contains(plain("[A-Z]")),
                contains(plain(r"\d")),
                contains(plain("[@$!%*?&]")),
            ]),
            "P@ssw0rd!",
        ),
        (
            "username-no-symbols-only",
            r"^(?![\-\_]*$)[A-Za-z0-9][A-Za-z0-9\-\_]{3,20}[A-Za-z0-9]$",
            RegexExpr::intersect([
                RegexExpr::complement(plain("[-_]*")),
                plain("[A-Za-z0-9][A-Za-z0-9_-]{3,20}[A-Za-z0-9]"),
            ]),
            "valid123",
        ),
    ] {
        workloads.push(Workload::custom(
            format!("popular/validate/{name}"),
            pattern,
            junco,
            Arc::from(sample.as_bytes()),
        ));
    }
    for workload in workloads {
        bench(criterion, workload);
    }
}

fn corpus(criterion: &mut Criterion) {
    let en = haystack("en-sampled.txt");
    let rust = haystack("rust-src-tools-3b0d4813.txt");
    let mut workloads = Vec::new();
    for (name, pattern, haystack) in [
        ("literal-hit", "Sherlock Holmes", Arc::clone(&en)),
        ("literal-miss", "ZZZYYYXXX999", Arc::clone(&en)),
        (
            "bounded-repeat-hit",
            r"\b[0-9A-Za-z_]{12,}\b",
            Arc::from(take_lines(&en, 2500)),
        ),
        (
            "alternation-hit",
            "Sherlock|Holmes|Watson|Irene|Adler",
            Arc::clone(&en),
        ),
        ("word-boundary-hit", r"\b[A-Z][a-z]+\b", Arc::clone(&en)),
        (
            "bounded-repeat",
            "[A-Za-z]{8,13}",
            Arc::from(take_lines(&en, 5000)),
        ),
        ("url", "https?://[a-zA-Z0-9./_?&=#%-]+", Arc::clone(&rust)),
        (
            "phone",
            r"(\(?\+?[0-9]*\)?)?[0-9_\- ()]{7,}",
            Arc::from(take_lines(&en, 5000)),
        ),
        (
            "dotstar-eq-redos",
            ".*=.*",
            haystack("cloud-flare-redos.txt"),
        ),
    ] {
        workloads.push(Workload::standard(
            format!("corpus/{name}"),
            pattern,
            haystack,
        ));
    }
    workloads.push(Workload::custom(
        "corpus/lookaround",
        r"(?<=\s)[A-Z][a-z]+(?=\s)",
        contains(plain(r"\s[A-Z][a-z]+\s")),
        en,
    ));
    for workload in workloads {
        bench(criterion, workload);
    }
}

criterion_group!(benches, popular_scan, popular_validate, corpus);

fn main() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            benches();
            Criterion::default().configure_from_args().final_summary();
        })
        .unwrap()
        .join()
        .unwrap();
}
