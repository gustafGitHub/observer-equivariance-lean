# observer-equivariance-lean

A Lean 4 + [mathlib](https://github.com/leanprover-community/mathlib4) formalization of the
strict classification theorem (Section 4) of

> G. Ullman, *Observer Equivariance as a Condition for Shared Physical Law*.
> Zenodo — concept DOI: `10.5281/zenodo.17077437`; version DOI: `10.5281/zenodo.<FILL-IN>`.

Everything lives in a single file: [`ObserverEquivariance.lean`](ObserverEquivariance.lean).

## What is formalized

For a *split principal `G`-fibration in groupoids* `p : O ⥤ S` together with a normalized,
transport-compatible basepoint section — bundled as the structure `OEData` — the file proves
the **theorem-level core of §4**:

- **`strict_lift` (§4.1):** every base autoequivalence of `S` lifts to a `G`-equivariant,
  cleavage-preserving bundle autoequivalence of `O` covering it.
- **`rigidity` (§4.2):** two such lifts of the same base symmetry differ by a *unique*
  normalized fiber translation `Λ d g` (`∃! g`).
- **The short exact sequence (§4.3)** in two forms:
  - elementary (`exact_sequence`): surjectivity of `Φ` plus the kernel characterization,
    stated with `∀/∃/↔`;
  - **as group theory:** `Φ : Aut□_G(O/p) →* Aut(S)` and `Λ : G →* Aut□_G(O/p)` are group
    homomorphisms (`MonoidHom`) with `Φ_surjective`, `ΛHom_injective`, and
    `ker_Φ_eq_range_Λ : (Φ d).ker = (ΛHom d).range`, i.e.
    `1 → G → Aut□_G(O/p) → Aut(S) → 1`.
- **`witness` / `witness₂`:** a concrete `OEData` for an arbitrary group `G`, and an explicit
  `|G| = 2` instance, so the theorem is non-vacuous (the assumptions are jointly satisfiable
  with a nontrivial structure group).

It does **not** formalize the physical specializations (Wigner–Uhlhorn, the fixed-spacetime
Lorentz model, the qubit phase model), the symmetry-breaking and observables sections, or the
philosophical discussion. Those appear in the paper but are out of scope for this development.

## Assumptions

Beyond the data and axioms of `OEData` (the split principal `G`-fibration of Definition 3.x
plus the normalized basepoint section of §4), the results use exactly two extra hypotheses:

- **`p_faithful : p.Faithful`** — the fibration is *thin*: at most one morphism between two
  objects over each base morphism (a torsor-groupoid fibration). This is the precise content
  of the "non-discrete" model; it holds for the paper's qubit, Lorentz and action-groupoid
  examples. `p.Full` is **not** assumed — it is derived (`OEData.isFull`).
- **`[IsConnected S]`** — `S` is connected. Used in `rigidity`/`exact_sequence`/
  `ker_Φ_eq_range_Λ`: connectedness gives constancy of the local element `g_s`, and
  non-emptiness gives its uniqueness. (`ΛHom_injective` needs only `[Nonempty S]`.)

Modelling choices worth flagging:

- `Λ_g` acts on in-fiber morphisms via a chosen vertical translation iso `ltrans` (the
  bundle's normalized translation datum), not via the cleavage `χ`. A cleavage-only definition
  is type-correct only for *discrete* fibers, and discrete fibers together with the flat
  basepoint section and connected `O` would force `G` trivial.
- `Aut□_G` is captured by `IsGEquivariant` (object-level `G`-equivariance) together with the
  predicate `PreservesCleavage`. Morphism-level `G`-equivariance is **derived** from
  `p_faithful`, not assumed.
- `Aut(S)` and `Aut□_G(O/p)` are the groups of **strict** (on-the-nose) automorphisms
  (`StrictAut S` / `AutBoxG d`), matching the paper's "chosen strict representatives of
  autoequivalences". Equivalences (`≌`) cannot form the group: they have no strict inverse,
  and `Λ_g ≅ 𝟭` would collapse the kernel.

## Sorry-free

The build is clean (no `sorry`, no `admit`). `#print axioms` on every top-level result:

```
'strict_lift'       depends on axioms: [propext, Classical.choice, Quot.sound]
'rigidity'          depends on axioms: [propext, Classical.choice, Quot.sound]
'exact_sequence'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Φ_surjective'      depends on axioms: [propext, Classical.choice, Quot.sound]
'ΛHom_injective'    depends on axioms: [propext, Classical.choice, Quot.sound]
'ker_Φ_eq_range_Λ'  depends on axioms: [propext, Classical.choice, Quot.sound]
'witness₂'          depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice` and `Quot.sound` are mathlib's three standard axioms; there is
no `sorryAx`.

## Building

- Toolchain: `leanprover/lean4:v4.31.0-rc1` (pinned in `lean-toolchain`; install via
  [elan](https://github.com/leanprover/elan)).
- mathlib is pinned in `lake-manifest.json` (rev `8834d3761934044a64c98afb757c1673fad03521`).

```sh
lake exe cache get   # download the pinned mathlib .olean cache
lake build           # compiles ObserverEquivariance.lean (~1 min once mathlib is cached)
```

> Local note: in this working copy, `.lake/packages` is a symlink to a sibling project's
> already-built mathlib (a developer optimization to avoid recompiling mathlib). For a fresh
> clone, remove that symlink and run `lake exe cache get` to fetch the pinned mathlib build,
> then `lake build`.
