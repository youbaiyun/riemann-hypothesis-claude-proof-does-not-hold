# On the Riemann Hypothesis: A Supplement on the Failure of Claude's Proof

**What this supplements** — the original's §1 (`UnusedSlot72` → `trivial`), §2 (the table of premises hidden in structure fields), §3 (the Satake vacuity claim and the weight-one renaming), and its "Lean either let it through, so it's A or B" section.
**Principle** — every conclusion of the original is kept. This supplement does exactly four things: **adds four pieces of evidence the original did not have**, **settles the A/B question as B**, **corrects six statements that could be dismissed with a single sentence**, and **supplies a line-by-line checkable evidence table**.
**How it was checked** — every quotation below is a real source line under `D:\LiManCX\lean\src`; line numbers are the files' actual line numbers.

---

## 0. The conclusion in one sentence

The original pinned down "three lines of code" (one `abbrev ... := True`, one `trivial`, one `Row0b` entry point). Those three lines are correct, but **they are not isolated instances: they are the same device operating on four different layers**:

| Layer | Mathematics it is supposed to carry | What the code actually says | Where |
|---|---|---|---|
| Geometric existence | "this divisor is realized by a geometric object" | `fun _ _ _ => True` | `Definitions\AutomorphicMembership\OverIx.lean:19` |
| Semipositivity and nefness | positivity of a Hermitian line bundle (the hardest analytic input in the whole chain) | `semipos/nefFib/arNef := fun _ => True` | `Proofs\FoundationProofs\ExistsProvisionalShimX.lean` |
| Literature theorems (60 fields) | 60 published theorems | 139 of 177 filling lemmas never use their hypotheses; the critical slot is `trivial` | `ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:666–726` |
| Entry point | "a proof with no hypotheses" | never compiled | see Supplement 4 |

**The three phrases in the original user's description each correspond to a real piece of code**: `anyGeometry` (layer 1), "degenerate model" (layer 2 — its real name is `provisionalShimX`; `geoDegenerate` does not exist in the repository), and "positivity conditions set to True" (the three fields of layer 2). Each is filled in below.

---

## Supplement 1 — `anyGeometry := fun _ _ _ => True`, the most literal hardcoded truth

The original's §2 table does not contain this item, yet it is the most explicit sentence in the entire repository: **the predicate "is geometric" is itself defined to be vacuously true**.

```lean
-- Definitions\AutomorphicMembership\OverIx.lean:14
abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

-- :16  what the author is willing to call geometric: there is a positive c
--      such that X is a geometric realization of Q, lying on a true surface
def geoOf (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D) : GeoP := fun D J X =>
  (∃ c : ℕ, 0 < c ∧ GlobalTheory.ShFam.IsGeoOf (Q D) J c X) ∧ GlobalTheory.ShFam.Pad.HasTrueSurf X

-- :19  the vacuously true geometry predicate
def anyGeometry : GeoP := fun _ _ _ => True
```

This is not an unused toy: it is a **field type** of a structure and the **actual argument** at more than twenty call sites.

```lean
-- :44  a structure field that takes the geometry predicate as its parameter
structure OAt (Γ : GeoP) ... (t : RowsT K w Z Wt p0) (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X     -- ← "geometric" is exactly this field
  lam : LamAre t.r.Z X

-- :49
def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X
```

`OComponent₂` (`NonzeroPlacesOverPrimes.lean:112`) is then fed to the reading machinery as genuine input: `NRead.of ... (Ox : OComponent₂)` (`HeightFunctions\OntoAlong.lean:100`) and `ExtensionReading.of ... (Ox : OComponent₂)` (`ThirdPlaceSeries\SideOf.lean:34`).

**Worse, it replicates itself**:

```lean
-- NotGeoClFalse.lean:21
inductive GeoCl (Γ : GeoP) : ∀ D, Pj.Core D → DivX D → Prop
  | base {D J X} : Γ D J X → GeoCl Γ D J X
  | step (N) (h) : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

-- :26
def geoCl (Γ : GeoP) : GeoP := GeoCl Γ
```

So `geoCl anyGeometry` is also a vacuously true predicate — **still vacuously true after any base change**. Where it is actually consumed:

```lean
-- Proofs\IwasawaDecomposition\MemberBuiltLinkedGeometric.lean:76 / LinkedBundleConstructionExists.lean:56
... (GlobalTheory.T.movable_geometric hL cDep anyGeometry) ...
-- OpenFirstParametersOfPublishedUE.lean:31–40: handed as an argument to discreteSeriesExists /
--   casselmanWallach / entry_hPA_at_parameters / entry_point_g_at_parameters
```

**One honest boundary must be stated**, or this point will be dismissed: the signature of `T.movable_geometric` (`SlotStageMovesGeometricStatement.lean:18`) is `∀ (Γ : GeoP), ...`, so it holds for **any** geometry predicate. Passing `anyGeometry` therefore violates no theorem. The real problem is this: **once "being geometric" can be filled with `True`, that quantification is empty** — it guarantees "for every predicate there is some position", not "this divisor really exists geometrically". Mathematically those are worlds apart; at the level of types they are indistinguishable.

---

## Supplement 2 — the degenerate model is `provisionalShimX`, and three positivity conditions are hardcoded to `True`

The original says that premises are legally hidden in structure fields. The heaviest case is in this section. `ShimX` is the structure that carries the entire arithmetic strategy (`Formalism\LocalRingCardinality\DataDIV.lean:159`, about 65 fields). The only "concrete witness" in the repository is:

```lean
-- Proofs\FoundationProofs\ExistsProvisionalShimX.lean:13
def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ)
    (hj : 1 ≤ j) (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  Comp := Unit          vol := 0             chern := 0            -- :170,:174,:176
  arDeg := fun _ _ => 0  arMix := fun _ _ _ => 0
  CurveHT := fun _ => Empty                     degHT := fun _ _ _ => 0      -- :191,:192
  CurveDR := fun _ => Empty                     degDR := fun _ _ _ => 0      -- :194,:195
  FibComp := fun _ => Empty                     fibInBd := fun _ _ => False  -- :197,:198
  Pt := Unit            XC := Unit              rfn := fun _ => Real.exp 1
  hLo := fun _ => 1     hUp := fun _ => 1       connN := fun _ => 0   curvN := fun _ => 0
  normDetInf/normDetT/normDetH := ... 1         htDetT := 0
  ALB := Unit           arSelf/arSelfC/geo/geoC/arVol := 0
  semipos := fun _ => True                      -- :236  ← semipositivity
  nefFib  := fun _ => True                      -- :237  ← nefness
  arNef   := fun _ => True                      -- :238  ← arithmetic nefness
  Mbar := fun _ _ _ => ()
```

Where those fields are declared (`DataDIV.lean`):

| Field | Line | Mathematical meaning | Filled with |
|---|---|---|---|
| `semipos : ALB → Prop` | 236 | semipositivity of a Hermitian line bundle (Bost / Gillet–Soulé type) | `fun _ => True` |
| `nefFib : ALB → Prop` | 237 | nefness of the fibre | `fun _ => True` |
| `arNef : ALB → Prop` | 238 | arithmetic nefness | `fun _ => True` |
| `CurveHT/CurveDR/FibComp : ℕ → Type` | 191,194,197 | height, de Rham and fibre components | `Empty` |
| `connN`, `curvN` | 214,215 | connection and curvature data | `0` |
| `ALB : Type` | 228 | the Albanese variety | `Unit` |

**The point is not merely "a field was filled with `True`"; it is that this object is really handed down the main chain as "that Shimura object"**:

```lean
-- ExistsProvisionalDivX.lean:213
def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

-- :221  the shv of provisionalDivX is smallShim; :296 exists_provisionalDivX closes with it
-- VarietyWithModels.lean:66  filler likewise uses provisionalShimX as shv,
--   and sets Mp := fun _ _ _ => Unit, CurveM := fun _ _ _ _ => Empty, degM := 0
```

At least four downstream sites consume it directly: `AutomorphicMembership\ExistsStagesClauses.lean:455`, `IwasawaDecomposition\ExistsEigenReadThirdLocal.lean:26`, `IndexZeroOffTwistedPlaces.lean:30`, `IndicesPairingLengthsVanishOffTwistedPlaces.lean:471`.

**Why this is more damaging than `UnusedSlot72`**: semipositivity is the one place in this strategy that cannot avoid real analysis — there is no shortcut. And the three theorems that consume it are the gate of the main chain:

```lean
-- Definitions\Divisors\SlopeTestRemainingChoices.lean:96–98
def Positive : Prop := ∀ Λ, ∃ s₀ > 0, ∀ B ≥ 2, ∀ (u : Wt Y) (s : ℚ), ...
    → NefCond Y B (A.sh u s) → Y.semipos (Y.Mbar B u s) ∧ Y.nefFib (Y.Mbar B u s)

-- :100–102  Squeeze (a Bost-type squeeze inequality)
-- :138–140  Inputs := ... ∧ Positive A ∧ Squeeze A ∧ Heights A ∧ Degrees A ∧ ...

-- WallSmallnessOfDegreesStatement.lean:8
theorem _root_.GlobalTheory.T.wall_smallness_of_degrees :
    ∀ (D) (Y : ShimX D.what₂.Tau) (A), 2 < D.R.f * (Y.N - 1) → Positive A → Squeeze A → ...
```

Both `Positive` and `Squeeze` are **definitions about `Y : ShimX`**, and `semipos`/`nefFib` are fields of `Y`. With `Y := smallShim D r`, those two fields are vacuously true, so `Positive`/`Squeeze` "hold" of the degenerate object — **and this derivation proves no semipositivity at all**.

(An honest boundary: `semipos` does have genuine consumers elsewhere, e.g. `EqOfSpecializesOfFinite.lean:310,318,331,394`, `FirstChernLeviEqConstant.lean:274,282`, `SemiposAtOfPositive.lean:159,163`. Those consumers show the field is load-bearing in other places — which is precisely why filling it with `True` on the "only concrete witness" constitutes a substantive substitution in the main chain, not a harmless placeholder.)

---

## Supplement 3 — quantifying the "60 literature-theorem fields": only 2 of them use their hypothesis

The original says that `BernsteinUnitaryProductIrreducible.lean:74` belongs to a hypothesis bundle "holding about 60 literature-theorem fields and gating the entire RH chain". The direction is right, but it can be turned into countable numbers.

**(1) The field count is exactly 60.** `ThirdPlaceSeries\BernsteinUnitaryProductIrreducible.lean:22–82`, from `clozelCohomological` to `localEulerChar`, is sixty fields line by line, one of which (`:74`) is the flattened `UnusedSlot72`.

**(2) The bundle is assembled inside the library itself.** `published_results_eigen` at `EveryCharacterOfLiteratureOfVWin.lean:666` fills it with sixty lines of the form `:= ..._of_literature O` (`:667–726`). That is to say: **"60 literature theorems" are not imported from the literature; they are 177 lemmas of the shape `X_of_literature (O) : X`.**

**(3) Most of those 177 lemmas never touch their hypothesis `O`.** Counting the file block by block (`:219–726`):

| Category | Count | Shape of the proof term |
|---|---|---|
| Never uses `O` at all | **139** | lands directly on `GlobalTheory.Published.*` or `PositivityTheory.Prw.*_holds` (e.g. `:295–296`, `partial_zeta_functional_equation_of_literature := PositivityTheory.Prw.partialZetaFunctionalEquation_holds`) |
| Mentions `O` | 38 | almost all merely forward it to another lemma, e.g. `cusp_u_of_literature := (UpperTheory.GalS.bridgeStar_alt (…gelfand_kazhdan_dual_of_literature O)).2` |
| **Actually extracts content from `O`** | **2** | `:283–284` `local_langlands_recT_exists_of_literature := O.localLanglandsExists`; `:286` uses `O.galoisRepOfPolarizedPairLit` |

In other words: `OpenLiteratureStatements` has only three fields (two copies of the same `One.M.Row`, plus `RecTExists`, `:215–218`), and of the sixty "literature theorems" only those 2 places extract anything from it. The other 58 fields are filled by another batch of in-repository `*_holds` theorems — **not literature, but yet more assumption slots from the same repository** (for instance `GlobalArtinReciprocityHolds.lean:5`, whose proof body is a single line: `:= CompanionTheory.FamInh.globalArtin`).

**(4) "The real version is right next door" is even stronger than the original says.** The same field name occurs in eight places in the repository, and the `UnusedSlot72` version is **not the only one but one of four**:

| Type | Where |
|---|---|
| `_root_.GlobalTheory.Published.UnusedSlot72` (flattened) | `ThirdPlaceSeries\BernsteinUnitaryProductIrreducible.lean:74`, `LocalTypeDictionary\BernsteinUnitaryProductIrreducibleBis.lean:198`, `BernsteinUnitaryProductIrreducibleTer.lean:64`, `GeometricLemma.lean:73` |
| `GlobalTheory.Published.SiegelEisensteinSimplePole` (real definition) | `Divisors\HypothesisBundleConversions.lean:117`, `GlobalTwisting\BhattScholzeCrystallineLattices.lean:71`, `DiscreteSeriesCoefficientsCuspidal.lean:434`, `GeneralHyps.lean:168` |

**The main chain takes the first of the four flattened copies**, while all four real-type copies sit quietly elsewhere. This is the direct trace of "it cannot pass mathematically, so it is routed around at the level of types" — and it happens four times, so it is not a typo.

---

## Supplement 4 — A or B? **B**

The original says one must first settle whether it is A or B. I checked: it is **B**.

| Check | Result |
|---|---|
| Top-level entries | only five: `.lake`, `src`, `lake-manifest.json`, `lakefile.toml`, `lean-toolchain` |
| `.git` / `.github` | **neither exists** (no VCS, no CI config, no release artefact) |
| Contents of `.lake` | **only `packages`** — no `build` |
| `.lake\packages\mathlib\.lake` | **does not exist** (mathlib is source only, no `.olean`) |
| `.olean` files in the repository | **0** (recursive count) |
| SHA-256 of this copy | `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` — **byte-identical** to the hash published in the mirror's README |
| README's own statement | says plainly "no independent build or review" and "Treat it as a claimed proof until it has been compiled and checked" |

Hence: **no build log, zero `.olean`, and the "hypothesis-free entry point" `Row0b recT` has never been checked by any compiler for even one step.** The original's wording for B ("no build log → that line saying verified on the release page is the author's self-assertion") can be kept as is, and can be put more strongly: this directory does not contain even one reusable build artefact, so any verification would have to full-build from mathlib sources.

One further correction is needed: the actual command to verify is not `lake build Main`. `Main.lean` is 12 lines; the weight is in `import Supplements.Kernels.MainTheoremsAll`, and `lakefile.toml` sets `moreLeanArgs ["--tstack=400000"]` and `maxHeartbeats 4000000`, with no mathlib cache to reuse. Real verification means "first `lake exe cache get` for mathlib `.olean`, then full-build 175,187 files": tens of hours and several GB of work.

---

## Supplement 5 — six statements that must be replaced (otherwise the whole piece is dismissed with "no such thing")

These are errors I found by checking the original line by line. **Correcting them does not weaken the original; it makes it impossible to wave away with one sentence.**

| # | As stated in the original | What the check found | Suggested replacement |
|---|---|---|---|
| 1 | `GeoOne` is assembled from `Steps + KSA11 + PlanEx` | **`KSA11` does not exist anywhere**; the real name is `KSAll` (`PackExOf.lean:93`), and the assembler is `geoOne_of_parts (Steps) (KSAll) (PlanEx)` (`GeoOneOfParts.lean:7`) | `Steps + KSAll + PlanEx` |
| 2 | "base-change `Field0K` / `InertOK` to a purpose-built QCM extension" | **`Field0K` / `Inert0K` do not exist**; the real counterpart is `GlobalTheory.Row9.FieldOK`, while `InertOK` itself does exist | use the real names; the conclusion about `InertOK` can stay (see #5) |
| 3 | the weight-one bottom layer is "about 370 lines" and "proves itself" | the file is 245 lines; the bottom is a genuine proof (`:74` onward, about 170 lines, calling five already-proved `etaleCorrespondence_*_statement` lemmas); the problem is **verbatim duplication in the two middle layers** | "245 lines of genuine proof plus two layers of renaming wrappers" |
| 4 | "the Satake matching may be vacuously true … this is my favourite attack point" | **the attack fails**: the quantification in `VBase` uses `UsPl` (`ApartAllEmpty.lean:24–25`), whose first conjunct is `IsSplitAt w`, so inert places never enter the `∀`; and there are at least four construction sites for `∃ B, SatU` (`ExistsTestOp.lean:58–59`, `AutomorphicLevelAwayNonsplit.lean:31–32,47`, `ExistsSatUOfUnderEq.lean:14`, `StConj.lean:47`) | delete this attack point, or restate it as "`SatU` covers only split places while non-split places are excluded outright by `UsPl` — this is a **range limitation** of the strategy, not a vacuity hole" |
| 5 | `InertOK` "all 8 hits are hypotheses" and `TLift` "is only a definition, never proved" | the 8 hits on `InertOK` are confirmed to be hypotheses or conjuncts with **no general construction**; the only proof is for a purpose-built extension (`ExistsQuadraticCMExtSplitAt.lean:12–149`) and is literally false for ℚ(i) (2 is totally ramified, a single prime (1+i), so `¬IsSplitAt` holds while `(2:ℤ) ∈ (2)`). `TLift` **does have a conditional proof** `tLift_of` (`SchurStep.lean:270–306`, nine hypotheses), but nothing in the repository calls it | "`InertOK` has no general proof; `TLift` has only a conditional proof and no consumer" |
| 6 | `Row0b recT` "is used three times" | false: `One.M.Row` (`SatakeParameters\RecT.lean:6`) is literally synonymous with it, and it is used far more than three times; the `⟨h, recTExists, h⟩` at `MainConclusion.lean:8` is simply two of the three `OpenLiteratureStatements` fields happening to coincide | "the load-bearing single premise stands; the 'three times' should be dropped" |

---

## Supplement 6 — evidence table (checkable line by line)

| ID | File:line | Content | What it adds |
|---|---|---|---|
| E1 | `AutomorphicMembership\OverIx.lean:19` | `def anyGeometry : GeoP := fun _ _ _ => True` | the vacuously true geometry predicate |
| E2 | `OverIx.lean:44–49` | `OAt.geo : Γ ...`; `OX Γ` | the vacuously true predicate used as a field type |
| E3 | `NotGeoClFalse.lean:21–28` | `inductive GeoCl` / `geoCl Γ` | vacuous truth propagates along base change |
| E4 | `HeightFunctions\OntoAlong.lean:100`, `ThirdPlaceSeries\SideOf.lean:34` | `NRead.of`, `ExtensionReading.of` take `OComponent₂` as input | the vacuously true predicate flows into the reading machinery |
| E5 | `SlotStageMovesGeometricStatement.lean:18` + `MemberBuiltLinkedGeometric.lean:76` | `movable_geometric : ∀ (Γ : GeoP), ...` instantiated with `Γ := anyGeometry` | the constraint reduces to zero |
| E6 | `DataDIV.lean:236–238` | `semipos / nefFib / arNef : ALB → Prop` | the three positivity fields declared |
| E7 | `ExistsProvisionalShimX.lean:13–68` | `provisionalShimX`: `Unit/Empty/0` plus three `fun _ => True` | the degenerate witness |
| E8 | `ExistsProvisionalDivX.lean:213,221,296`; `VarietyWithModels.lean:66` | `smallShim` / `shv` / `exists_provisionalDivX` / `filler` | the degenerate witness is used |
| E9 | `SlopeTestRemainingChoices.lean:96–98,100–102,138–140`; `WallSmallnessOfDegreesStatement.lean:8` | `Positive` / `Squeeze` / `Inputs` / `wall_smallness_of_degrees` | positivity becomes the gate |
| E10 | `BernsteinUnitaryProductIrreducible.lean:22–82` | `UnitaryGroupThirdPlaceHypotheses`, 60 fields | the size of the literature bundle |
| E11 | `EveryCharacterOfLiteratureOfVWin.lean:666–726` | `published_results_eigen`: sixty lines of `_of_literature O` | the bundle is assembled in-repository |
| E12 | same file, `:219–726` census | 177 `_of_literature`: 139 never touch `O`, 38 mention it but mostly forward it, **only 2 extract content** (`:283–284`, `:286`) | "literature theorems" is a misnomer |
| E13 | same file, `:505–506,718`; `DiscreteSpectrumResidualClassification.lean:7` | `siegel_eisenstein_simple_pole := trivial`, of type `UnusedSlot72 := True` | the original's three lines of code |
| E14 | the 8 `siegelEisensteinSimplePole` fields (4 real / 4 flattened, see table) | the real-type copy is right next door | routing around at the level of types |
| E15 | `.lake` has no `build`, mathlib has no `.olean`, 0 `.olean` in the repository | never compiled | settles B |

---

## Closing — the original's sentence can be upgraded

The original says: "Three lines of code, reproducible, no compilation needed, and no need for it to fail in the code."

**It can now be said more precisely**: not three lines, but four layers —

1. **Geometry layer**: `anyGeometry` makes "being geometric" vacuously true (E1–E5);
2. **Analysis layer**: `provisionalShimX` makes semipositivity and nefness vacuously true (E6–E9);
3. **Literature layer**: of the 60 fields only 2 use their hypothesis, the critical slot is `trivial`, and the real-type copy sits right beside it (E10–E14);
4. **Entry layer**: none of this was ever compiled (E15).

Take any one layer and "this repository proved RH" fails. With all four at once, it is not "a contested proof" but **a formal artefact in which the mathematical content has been replaced by `True`**.

---

> **Boundary statement** — This supplement does not claim that the Riemann Hypothesis is false. It claims only that the proof Claude produced does not hold, i.e. that this repository has not proved the Riemann Hypothesis. Every quotation is taken from an actual source line under `D:\LiManCX\lean\src`; `geoDegenerate` does not exist in the repository, and its equivalents are `anyGeometry` and `provisionalShimX`.
