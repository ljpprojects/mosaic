extern crate mosaic_lang;

use criterion::{Criterion, criterion_group, criterion_main};
use mosaic_lang::frontend::lexer::tests;

fn criterion_benchmark_complex_escapes_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer complex escapes test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_complex_parameterised_escapes() })
    );
}

fn criterion_benchmark_simple_escapes_param_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer simple escapes parameterised test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_simple_parameterised_escapes() })
    );
}

fn criterion_benchmark_simple_escapes_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer simple escapes test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_simple_escapes() })
    );
}

fn criterion_benchmark_templates_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer templates test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_templates() })
    );
}

fn criterion_benchmark_static_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer static test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_static() })
    );
}

fn criterion_benchmark_raw_1000(c: &mut Criterion) {
    c.bench_function(
        "StringLexer raw test x1000",
        |b| b.iter(|| for _ in 0..1000 { tests::string_lexer_raw() })
    );
}

criterion_group!(
    benches,
    criterion_benchmark_templates_1000,
    criterion_benchmark_complex_escapes_1000,
    criterion_benchmark_simple_escapes_param_1000,
    criterion_benchmark_simple_escapes_1000,
    criterion_benchmark_static_1000,
    criterion_benchmark_raw_1000
);

criterion_main!(benches);