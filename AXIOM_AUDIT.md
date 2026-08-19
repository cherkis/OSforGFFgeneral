# Axiom audit

The build graph of this library declares **zero custom axioms**: `grep -rn '^ *axiom '
OSforGFF` is empty (as is `Legacy/`, which is off the import graph). Every headline theorem
depends on exactly Lean's three core axioms and nothing else:

```
propext, Classical.choice, Quot.sound
```

| Headline theorem | `#print axioms` |
|---|---|
| `gaussianFreeField_satisfies_all_OS_axioms_generic` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_of_dim` (every `d ≥ 2`) | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim4` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim3` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim2` | the 3 core axioms |
| `gaussianFreeField_satisfies_all_OS_axioms_dim5` | the 3 core axioms |

In particular, the Minlos theorem and the nuclear-space structure of Schwartz space are consumed
from the external [bochner](https://github.com/mrdouglasny/bochner) and
[gaussian-field](https://github.com/mrdouglasny/gaussian-field) libraries as *proven theorems*,
not assumptions — the 3-core-axiom footprint above certifies this transitively.

## How this is enforced

- **Build-time (the hard gate):** `OSforGFF/Guardrails.lean` is part of the root import graph, so
  `lake build` compiles it. Its `#guard_msgs` blocks freeze both the axiom footprint and the exact
  statement type of all six headline theorems; any drift fails the build.
- **Source-level:** `bash scripts/check-guardrails.sh` scans every module reachable from
  `OSforGFF.lean` for `axiom` declarations, escape hatches (`native_decide`, `unsafe`,
  `implemented_by`, `extern`), and `sorry`/`admit`, stripping comments first so prose that
  merely names them is not a false positive. The check is absolute rather than relative to a
  baseline revision, so it cannot silently pass by losing its reference point; set
  `GUARDRAIL_BASE=<rev>` to additionally report which violations a given range introduced.
  `OSforGFF/Legacy/` is exempt — deliberately off the import graph, never compiled.
- **CI:** both of the above run on every push and pull request
  ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)), which also replays the built
  environment through an external kernel check (`leanchecker`).
- **Manual spot-check:** run `#print axioms gaussianFreeField_satisfies_all_OS_axioms_of_dim`
  (and the other five names above) in a scratch file with `import OSforGFF.OS.Master` via
  `lake env lean`; each must report exactly `[propext, Classical.choice, Quot.sound]`.
