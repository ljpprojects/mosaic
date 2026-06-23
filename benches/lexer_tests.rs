extern crate mosaic_lang;

use criterion::{Criterion, criterion_group, criterion_main};
use mosaic_lang::frontend::lexer::tests;

fn criterion_benchmark_complex_escapes(c: &mut Criterion) {
    c.bench_function(
        "StringLexer complex escapes test",
        |b| b.iter(|| tests::string_lexer_complex_parameterised_escapes())
    );
}

fn criterion_benchmark_simple_escapes_param(c: &mut Criterion) {
    c.bench_function(
        "StringLexer simple escapes parameterised test",
        |b| b.iter(|| tests::string_lexer_simple_parameterised_escapes())
    );
}

fn criterion_benchmark_simple_escapes(c: &mut Criterion) {
    c.bench_function(
        "StringLexer simple escapes test",
        |b| b.iter(|| tests::string_lexer_simple_escapes())
    );
}

fn criterion_benchmark_templates(c: &mut Criterion) {
    c.bench_function(
        "StringLexer templates test",
        |b| b.iter(|| tests::string_lexer_templates())
    );
}

fn criterion_benchmark_static(c: &mut Criterion) {
    c.bench_function(
        "StringLexer static test",
        |b| b.iter(|| tests::string_lexer_static())
    );
}

fn criterion_benchmark_raw(c: &mut Criterion) {
    c.bench_function(
        "StringLexer raw test",
        |b| b.iter(|| tests::string_lexer_raw())
    );
}

criterion_group!(
    benches,
    criterion_benchmark_templates,
    criterion_benchmark_complex_escapes,
    criterion_benchmark_simple_escapes_param,
    criterion_benchmark_simple_escapes,
    criterion_benchmark_static,
    criterion_benchmark_raw
);

criterion_main!(benches);