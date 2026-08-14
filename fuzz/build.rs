//! Supplies libFuzzer's `main` to this package's binaries only.
//!
//! `libfuzzer-sys` gets `main` from a static archive that no Rust code references, so on MSVC the
//! linker has to be told to pull it in. cargo-fuzz can do that itself, but only as a global
//! `RUSTFLAGS` link argument, which would also land on the `cdylib` crate-type of
//! `junco-rust-validator` (required by napi) — and a DLL that references `main` fails to link with
//! `LNK2001`. `cargo::rustc-link-arg-bins` scopes the argument to the fuzz binaries instead.
//!
//! Windows therefore builds with `cargo fuzz run git_policy --no-include-main-msvc`; other
//! platforms are unaffected and use the plain invocation.

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    if std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc") {
        println!("cargo::rustc-link-arg-bins=/include:main");
    }
}
