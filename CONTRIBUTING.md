# How to contribute to this project

First of all, thanks for being interested in C±.

I am happy you are here and look forward to reviewing and merging your contributions to the project.

A few notes on how to make this process as easy and seamless as possible.

## Coding style

I hate arguing over coding style, so I just automate it away. My local flow uses [precommit](https://pre-commit.com/) and I encourage you to use it as well. By default it will run `cargo format`, `cargo check` and `cargo clippy`. If those all pass, then you're golden. The same checks will happen at GitHub and if they fail, I will ask you to resubmit until they pass. Run them locally and spare yourself (and me) the trouble.

## Licensing

This project is licensed under Apache 2.0. I ask that you submit patches under your real name and under the same license. If you can't do either of those, I can't accept your patch. A [DCO](https://developercertificate.org/) is sufficient for this purpose.

## Testing

There are three testing styles in this project:
- **inline unoptimized JIT tests**: these are the original test format, but unless you need to do interesting checks on the compiler's output (which nobody does anyway), they are discouraged;
- **out of band JIT tests**: these are great for simple tests that can fail but won't bring the entire compiler down (e.g. no unreachable code, no failed asserts, ...); they will run with and without optimization;
- **out of band a.out tests**: these are great if you're testing things that can easily crash (LLVM edge cases, failed assertions, memory smashers) and will also run with and without optimization.

When you submit a patch, make sure no tests break. Add tests for your work. If you can't add a test, this will make the patch subject to extra scrutiny before being merged.

## Large-scale changes

While contributions are welcome, some things may be explicitly out of scope for one reason or another, so please reach out before you embark on any major architectural change. Maybe I am thinking about it already, maybe I am thinking of doing it differently, or maybe I'd rather not have it there at all. Reaching out ahead of time is the best way to avoid wasting time.

Thanks for reading and happy hacking.
