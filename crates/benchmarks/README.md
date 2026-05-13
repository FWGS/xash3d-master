# Benchmarks

Run all benchmarks, compare with the baseline `base` and save results to the baseline `base`:

```
cargo bench --bench protocol
```

Run all benchmarks, compare with the baseline `base` and save results to the baseline `opt`:

```
cargo bench --bench protocol -- -s opt
```

Run all benchmarks and compare with the baseline `opt` without saving results of this run.

```
cargo bench --bench protocol -- -b opt
```

Run all benchmarks for master packets and compare with a baseline `base`:

```
cargo bench --bench protocol -- master/ -b base
```

Run decode benchmarks for ChallengeResponse master packet:

```
cargo bench --bench protocol -- master/ChallengeResponse/decode
```
