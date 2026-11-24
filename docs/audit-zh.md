# 写死恒真之后：对 CocoSgt/riemann-hypothesis-lean 的数学审计报告

**——为什么一份包含 175,187 个 Lean 文件、零 `sorry`、零 `axiom` 的"黎曼猜想证明"，在数学上并不成立**

审计对象：`https://github.com/CocoSgt/riemann-hypothesis-lean`（Levent Alpöge 的 Lean 证明的镜像）
审计副本：`D:\LiManCX\lean`（解压自 `lean.tar.gz`，239,275,554 字节）
副本 SHA-256：`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`（与镜像 README 公布值一致）
审计日期：2026-11-24　　审计方式：全量静态阅读 + 脚本扫描 + 四路独立交叉审计（**未编译**，理由见 §1.3）

---

## 摘要

本报告不讨论"黎曼猜想是否为真"。本报告讨论的是一个更窄、也更容易判定的命题：

> **该仓库给出了黎曼猜想（RH）的数学证明。**

结论：**不成立。** 理由有两条，彼此独立，各自足以否定上述命题。

**理由一（承重命题未证）。** 全部 175,187 个文件、909,822 行 `import` 最终压在一个命题上：`UpperTheory.GalStar.Row0b recT`。它不是 RH，而是 Fontaine–Mazur 型局部-整体 Langlands 对应的全称版本——对任意 CM 域 $E$、任意 $a\ge 1$、任意正则代数尖点自守表示，都存在满足 crystalline / de Rham / 权重条件的 $\ell$-adic Galois 表示。这是一个至今无人证明的猜想，且**严格强于** RH。仓库对它的处理不是"证明"，而是**构造**：它把这个结论写成 `def`，再用一串定理把它的项拼出来。RH 只是这条链末端的一行推论（`N=1, χ=1`）。

**理由二（关键条件写死恒真）。** 即便退一步，接受"从 `Row0b` 能推出 RH"这一形式推导，这条链所证明的也**不是它命名的那个数学命题**。审计发现，链条中承担数学内容的三个输入层——几何见证、分析正性、文献定理——在源码里被替换成了恒真谓词、退化见证与 `trivial`：

- 几何谓词 `anyGeometry : GeoP := fun _ _ _ => True`，对一切输入返回"成立"（`OverIx.lean:19`）；
- 唯一的 `ShimX` 具体见证 `provisionalShimX` 把分量类型设为 `Unit`、曲线类型设为 `Empty`、全部陈数与算术度设为 `0`、**半正性 / 纤维 nef / 算术 nef 三个正性谓词直接设为 `fun _ => True`**（`ExistsProvisionalShimX.lean:13–68`）；
- 一条名为 `siegel_eisenstein_simple_pole` 的"文献定理"证明项是 `trivial`，因为它所在槽位的类型被定义为 `Prop := True`（`EveryCharacterOfLiteratureOfVWin.lean:505–506`，`UnusedSlot72`）。

三段引文并置，本报告的核心判断就可以一句话说完：**当"几何存在"被写成 `True`、"半正性"被写成 `True`、"文献定理"由 `trivial` 填充之后，从这些前提出发的任何推导，其前提里已经不含被命名的数学内容；因此推导出来的东西，无论形式多完整，都不构成对那个数学命题的证明。**

本报告同时明确它**不**主张什么（§10）：不主张 RH 为假；不主张仓库是空壳或作弊；不主张归约步骤（`EveryCharacter ⇒ RH`）有错——那一步是真的。报告的可反驳条件写在 §10.4。

---

## 1. 审计对象、方法与边界

### 1.1 对象的身份与规模

| 项目 | 数值 | 核验方式 |
|---|---|---|
| `.lean` 文件数 | 175,187 | 全盘计数，与网络流传审计一致 |
| `import` 行数 | 909,822 | 同上 |
| 主目录分布 | Development 141,928；Formalism 18,254；GroundTheory 8,507；ReciprocityTheory 3,845；CompanionTheory 2,027；PositivityTheory 449；Lemmata 167；BuildAid 5；Supplements 3 | 逐目录计数 |
| 工具链 | `leanprover/lean4:v4.33.1` | `lakefile` 与本地 `elan` |
| Mathlib 版本 | rev `0df444a360eaa60ab8c11dca51a86af692955474` | `lake-manifest.json` |
| 编译参数 | `moreLeanArgs ["--tstack=400000"]`，`maxHeartbeats 4000000` | `lakefile` |
| 仓库元数据 | 公开，2026-11-20 创建，552 stars / 88 forks | GitHub API |

压缩包 SHA-256 与镜像 README 公布值逐位一致，可以排除"审计了错版本"这一可能。

### 1.2 逐条核对的逃逸舱口（全部为零）

一份"证明"若有 `sorry`、`axiom`、`native_decide`、`unsafe`、`@[implemented_by]`，可以立刻判死。本仓库在这一层是干净的：

| 逃逸舱口 | 全库命中 |
|---|---|
| `sorry` / `admit`（真逃逸） | 0 / 0（`admit` 的命中全是命名空间 `CompanionTheory.D.gk.admitted`） |
| `axiom` / `constant` / `opaque` 声明 | 0 / 0 / 0（仅一处结构体字段名叫 `axioms`，`CMModuli\ThetaCosetLabels.lean:234`） |
| `native_decide` | 0 |
| `unsafe` / `@[extern]` / `implemented_by` | 0 / 0 / 0 |
| `set_option debug.*` / `skipKernelTC` | 0 / 0 |
| `maxRecDepth` 覆写 | 0 |
| 自定义 `addDecl` | 1 处：`CutCptCopy.lean:78,82`，做的是带 `subst` 的重命名拷贝，内核仍校验 |

另有 4 处 `set_option maxHeartbeats 0 in`（`PtfsShaFinal.lean:26`、`CutMainCpt.lean:944`、`UniformizerClauseOfAdmitted.lean:48` 与其 `Alt.lean:51`），属于长证明的常见放宽，不构成逃逸。

**这一节的意义在于把争论挪到正确的位置。** 本报告的批评与"它写了 `sorry`"无关。问题不在内核，在**命题本身**：被写进类型签名的那些谓词，其定义体已经把数学内容抽空了。Lean 会忠实地检查"从 `True` 能推出 `True`"，它不会替我们检查"这个 `True` 是否就是半正性"。

### 1.3 未编译：一个必须交代的边界

本副本**从未编译**：

- 项目根目录 `D:\LiManCX\lean\.lake` 下只有 `packages`，没有 `.lake\build`；
- Mathlib 本身也只有源码（`.lake\packages\mathlib`），没有 `.lake\packages\mathlib\.lake\build`，即没有 `.olean`；
- 镜像 README 自己写明了这一点，并要求"在编译与检查之前，把它当作一个**声称的**证明（claimed proof）"。

因此本报告的全部结论都是**源码级（statement-level）结论**：它断言的是"即便编译通过，这份产物也不是 RH 的数学证明"，而不是"它编译不过"。§10.3 会说明，后者恰恰不是本报告需要的论点。

---

## 2. 先把命题摆对：它到底证了什么

### 2.1 顶层陈述是对的

`src\Main.lean` 只有 12 行：

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

`RiemannHypothesis` 来自 Mathlib，定义在 `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`：

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2*(n+1)) → s ≠ 1 → s.re = 1/2
```

我全库检索过同名遮蔽：仓库只定义过 `RiemannHypothesisOfLowerBounds`、`RiemannHypothesisOfHalfLinks`、`GrowthBoundAndRiemannHypothesis` 等**衍生**命题，**没有**重新定义 `RiemannHypothesis`。所以顶层陈述就是真的 RH，没有被偷换成弱命题。这一点必须给作者记上。

### 2.2 推导链：三段，其中一段是真的

```
Main.lean:4            riemannHypothesis      := rhOfAll
MainTheorems.lean      rhOfAll                := Formalism.VW.rh_of_every allChi
MainTheorems.lean      allChi                 : EveryCharacter := FinalTheorems.everyCharacter
MainConclusion.lean:10 everyCharacter         := everyCharacter_of_row galoisLocalGlobalStrong_recParameter
MainConclusion.lean:7  everyCharacter_of_row  : (Row0b recT) → EveryCharacter
RowSrc.lean:6          galoisLocalGlobalStrong_recParameter : Row0b recT
GaloisRepresentationsOfThetaLift.lean:6         := galoisLocalGlobalStrong_of_geometry_lift Geo.geoOne_holds tLiftK
Development.lean:27    galoisLocalGlobal_of_geometry_lift : GeoOne → TLiftK → Row0 recT
WeightOneGeometricRealization.lean:11  geoOne_holds : GeoOne
```

末段 `EveryCharacter ⇒ RH` 是**真证明**，值得单独指出，因为它是全仓库最干净的一段：

```lean
-- Formalism\GammaFactorNonvanishing\RhOfRight.lean:5
theorem Formalism.VW.rh_of_right
    (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1/2) with hlt | heq | hgt
  · -- 用函数方程 s ↦ 1-s 把左半平面拉回右半平面
    ...
-- Formalism\GammaFactorNonvanishing\CritLine.lean:29
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
```

它合法地使用了 ζ 的函数方程、Γ 因子非零、`cos` 零点位置。这一步没有问题。

**问题全在它前面。** 链条把 RH 归约为 `EveryCharacter`（所有 Dirichlet L 函数在 $\Re s>1/2$ 非零），再把 `EveryCharacter` 归约为 `Row0b`。而 `Row0b` 不是一个已知定理，是一个猜想：

```lean
-- TypeConditions\WeightsConjBis.lean:69
def Row0b : Prop :=
  ∀ (E Ω) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
      (CG.mk π).IsRegAlg → ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        PropsB Rc π ι r wt HT
```

量词结构是 `∀ CM 域 E, ∀ a ≥ 1, ∀ 正则尖点表示 π, ∀ 极化对 (π,χ), ∃ Galois 表示 r`。这不是"某个已发表定理的形式化"，而是**对全部 CM 域、全部维数的全称断言**——它蕴含 RH，但不被 RH 蕴含，且远比 RH 强。数学界没有任何一个结果能给出它。

于是本报告的第一条结论可以精确表述：

> 该仓库实际证明的是 `(Row0b recT) ⇒ EveryCharacter ⇒ RH`。其中第二段为真，第一段依赖 `Row0b`，而 `Row0b` 在全库中只被**定义**与**构造项**（`Development.lean:27–31`），从未被证明。因此仓库证明的是"若 Fontaine–Mazur 型局部-整体 Langlands 成立，则 RH 成立"——一句正确的蕴含，而不是"RH 已证"。

> 附带说明：网络流传的审计把"未被证明的前置"数成"只有一条、且被用了 3 次"。前半句成立，后半句不成立：`Row0b recT` 在文件的字面上与 `UpperTheory.One.M.Row` 同义（`SatakeParameters\RecT.lean:6`），但全库对它的使用远多于三处；`MainConclusion.lean:8` 那一次 `⟨h, recTExists, h⟩` 只是 `OpenLiteratureStatements` 的三个字段恰好两个是同一命题。

### 2.3 那么"写死恒真"究竟如何使结论不成立

有人会立刻反驳：**`def C : Prop := True` 不会让假命题变得可证；如果链条真能走到 RH，那么 RH 就被证明了，你说破天也没用。**

这个反驳对"纯逻辑"是成立的，但它建立在一个错误前提上：**以为链条末端是要证的那个命题。** 而事实上，链条每一格证的是**带名字的中间命题**，名字承载数学内容，定义体却不承载。举例：

- 某个定理叫 `movable_geometric`，数学上应当是"该除子对应的几何对象可以沿基变换移动"。它的签名是 `∀ (Γ : GeoP), PositionMv (prmR ... (geoCl Γ)).s`——对**任意**几何谓词 `Γ` 成立。既然对任意 `Γ` 成立，它对 `Γ := fun _ _ _ => True` 成立；而这个 `True` 恰恰被用在真正的消费点上（`MemberBuiltLinkedGeometric.lean:76`、`LinkedBundleConstructionExists.lean:56`）。于是"几何性"这个约束在任何地方都不再约束任何东西。
- 某个结构体 `ShimX` 有字段 `semipos : ALB → Prop`，数学上是 Hermitian 线丛的半正性（Bost / Gillet–Soulé 型定理的结论，是整个算术策略里最硬的分析输入）。仓库提供的唯一具体见证把该字段填成 `fun _ => True`。于是依赖 `Y.semipos L` 的定理 `Positive`、`Squeeze` 全部在"由一个分量、零曲线、零度数的退化模型"上被满足。

这就是"写死恒真"的准确含义：**它不是伪造一个证明项，而是把类型签名里的数学内容抽走，使定理成为关于 `True` 的真命题，然后让调用者以为自己在用原命题。** Lean 检查通过，数学没有前进。

下面五节给出逐行证据。

---

## 3. 机制一：几何见证被写成恒真谓词 `anyGeometry`

### 3.1 定义

`Definitions\AutomorphicMembership\OverIx.lean` 共 53 行，其中三行是全文的关键：

```lean
-- :14
abbrev GeoP : Type 1 := ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop

-- :16  真正的几何谓词：要求 X 是某个 Q 的几何实现，并且是真曲面
def geoOf (Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D) : GeoP := fun D J X =>
  (∃ c : ℕ, 0 < c ∧ GlobalTheory.ShFam.IsGeoOf (Q D) J c X) ∧ GlobalTheory.ShFam.Pad.HasTrueSurf X

-- :19  恒真几何谓词
def anyGeometry : GeoP := fun _ _ _ => True
```

`GeoP` 是"几何谓词"的类型：给定一个基、一个核心数据、一个除子，断言它具备某种几何性。`geoOf Q` 是作者愿意承认的那种几何性（存在正整数 $c$，使 $X$ 是 $Q$ 的几何实现，且 $X$ 落在真曲面上）。`anyGeometry` 则对**一切**基、**一切**核心、**一切**除子（包括完全非几何的垃圾对象）返回 `True`。

### 3.2 它如何被使用：作为"几何见证"递给上层结构

```lean
-- OverIx.lean:44
structure OAt (Γ : GeoP) ...
    (t : RowsT K w Z Wt p0) (X : DivX (w.D Z)) : Type 1 where
  geo : Γ (w.st Z).toD7 t.r.z.core.toCore X     -- ← 几何性，就是这个字段
  lam : LamAre t.r.Z X

-- OverIx.lean:49
def OX (Γ : GeoP) : OComponent₂ := fun _ _ _ _ _ _ _ O t => OAt Γ t O.X
```

`OComponent₂` 是"自守成员性"的一个组件（`NonzeroPlacesOverPrimes.lean:112`），它作为输入流入读数机器：`NRead.of ... (Ox : OComponent₂)`（`OntoAlong.lean:100`）、`ExtensionReading.of ... (Ox : OComponent₂)`（`ThirdPlaceSeries\SideOf.lean:34`）。也就是说，整条自守侧的计算，其"这个除子确实是几何对象的实现"这一前提，是由 `OAt` 的 `geo` 字段承担的；而当 `Γ := anyGeometry` 时，这个字段的类型就是 `True`，证据是 `trivial`。

`anyGeometry` 的实际传参点（部分）：

| 位置 | 传参内容 |
|---|---|
| `AutomorphicMembership\GKeyFin.lean:22` | `prmR ... (geoCl anyGeometry)` |
| `AutomorphicMembership\MultW.lean:45` | 同上 |
| `AutomorphicMembership\NotLamAreShift.lean:153` | `∃ l, Nonempty (OAt anyGeometry t ...)` |
| `AutomorphicMembership\ParMem.lean:137` | `prm0 hL := prmR (NEb hL) SExt.none (geoCl anyGeometry)` |
| `DivisorProofs\LinkedBundleConstructionExists.lean:28–31,51,56` | `T.movable_geometric hL cDep anyGeometry` |
| `DivisorProofs\LinkedBundleConstructionExistsStatement.lean:12` | 出版级陈述的结论里直接写着 `geoCl anyGeometry` |
| `DivisorProofs\NonemptyHypsOfPublishedUE.lean:30,38,41` | 同上 |
| `DivisorProofs\OpenFirstParametersOfPublishedUE.lean:31–40` | 把 `anyGeometry` 递给 `P.discreteSeriesExists`、`P.casselmanWallach` 等"已发表定理" |

最后一行尤其值得停一下：`OpenFirstParametersOfPublishedUE.lean` 在调用 `discreteSeriesExists`、`casselmanWallach` 这类以真实数学家命名的定理时，几何参数位上传的是 `geoCl anyGeometry`。**"已发表定理适用于此几何对象"这件事，是被 `True` 满足的。**

### 3.3 `geoCl` 的闭合：把 `True` 沿基变换传播

`Definitions\AutomorphicMembership\NotGeoClFalse.lean:21–28` 定义了一个归纳闭包：

```lean
inductive GeoCl (Γ : GeoP) : ∀ D : D7, Formalism.L2.Pj.Core D → DivX D → Prop
  | base : Γ D J X → GeoCl Γ D J X
  | step (N) (h) : GeoCl Γ D J X → GeoCl Γ (setDiv D N h) (coreS N h J) (divTr N h X)

def geoCl (Γ : GeoP) : GeoP := GeoCl Γ
theorem geoCl_of (h : Γ D J X) : geoCl Γ D J X := GeoCl.base h
```

`step` 让几何性沿"改变除子 / 改变核心数据"的操作传播。当 `Γ = anyGeometry` 时，归纳的基例是 `True`，于是"这个对象在任何基变换之后都是几何的"这句话的证明是一次 `trivial` 加若干次 `step`。**一个本应对对象施加限制的谓词，变成了对所有对象无条件成立的谓词。**

### 3.4 数学上发生了什么

- 若消费点的定理是 `∀ Γ, ...`，则它没有区分"几何的"与"非几何的"对象——这条链关于几何什么都没说，几何词汇只是装饰；
- 若消费点把 `Γ` 固定为 `anyGeometry`（如 §3.2 表中各点），则"这个除子是几何实现"这一前提由 `True` 兑现，**该前提的数学内容为零**。

两种读法都导向同一结论：**几何侧不承载内容**。这不是"证明写错了"，而是"证明所谈论的对象不再是被命名的那个对象"。

---

## 4. 机制二：退化模型充当几何对象，三个正性条件直接写死 `True`

这是全报告最重的一节。用户所提供的直觉——"退化模型被用作几何见证，正性条件直接设为 `True`"——在源码中是逐字成立的，只是对象名不叫 `geoDegenerate`。

### 4.1 `ShimX`：一个承载整条算术策略的结构体

`Formalism\LocalRingCardinality\DataDIV.lean:159` 起，`structure ShimX (Tau : Type) [Fintype Tau]` 用约 65 个字段描述一个 Shimura 型对象的全部算术几何数据（行号为实际行号）：

| 行 | 字段 | 数学含义 |
|---|---|---|
| 170 | `Comp : Type` | 分量集合 |
| 174 | `vol : ℝ` | 体积 |
| 176 | `chern` | 陈特征 |
| 181 | `arDeg` | 算术度 |
| 185 | `arMix` | 算术混合（HT/DR 两支） |
| 191,194 | `CurveHT / CurveDR : ℕ → Type` | 两类曲线（作为高度机器的被测对象） |
| 197–198 | `FibComp / fibInBd` | 纤维分量及其有界性 |
| 200 | `Pt : Type` | 点集 |
| 202–206 | `phiDR/phiMod/phiFr` | 相位数据 |
| 208–217 | `XC, rfn, hLo, hUp, connN, curvN, compOf` | Chern 联络点、正规化因子、范数上下界、**联络范数与曲率范数** |
| 218–226 | `normDetInf/T/H, htDetT` | 行列式范数与高度 |
| 228–235 | `ALB, arSelf, arSelfC, geo, geoC, arVol` | 算术线丛、算术自交、几何度、算术体积 |
| **236–238** | **`semipos, nefFib, arNef : ALB → Prop`** | **半正性、纤维 nef、算术 nef** |

### 4.2 唯一的"具体见证"把所有内容抹成零与 `True`

`Proofs\FoundationProofs\ExistsProvisionalShimX.lean:13`：

```lean
def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ)
    (hj : 1 ≤ j) (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  ...
  Comp := Unit                     -- 只有一个分量
  vol := 0                         -- 体积 0
  chern := 0                       -- 陈特征恒零
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0            -- 算术度恒零
  arMix := fun _ _ _ => 0
  CurveHT := fun _ => Empty        -- 没有曲线
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty        -- 没有纤维
  fibInBd := fun _ _ => False      -- 纤维有界性恒假
  Pt := Unit
  phiDR := fun _ _ _ => 0
  ...
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  connN := fun _ => 0              -- 联络范数 0
  curvN := fun _ => 0              -- 曲率范数 0
  ...
  ALB := Unit                      -- 只有一条"线丛"
  arSelf := fun _ => 0
  geo := fun _ => 0
  arVol := fun _ => 0
  semipos := fun _ => True         -- ← 半正性：恒真
  nefFib := fun _ => True          -- ← 纤维 nef：恒真
  arNef := fun _ => True           -- ← 算术 nef：恒真
  Mbar := fun _ _ _ => ()
```

这个定义本身是良构的：`ShimX` 的字段都只是 `Type`/`ℝ`/`Prop`，填零与填真都能通过类型检查。问题不在类型，在**它被当成了谁**。

### 4.3 它被当成了"那个 Shimura 对象"

```lean
-- ExistsProvisionalDivX.lean:213
def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

-- ExistsProvisionalDivX.lean:221  provisionalDivX ...
    shv := fun S _ => smallShim D S.rank
    shv_N := fun _ _ h => max_eq_left h
    shv_lev := fun _ _ => rfl

-- ExistsProvisionalDivX.lean:296
theorem exists_provisionalDivX : ∀ D : D7, (...) → ∃ X : DivX D, ...
-- VarietyWithModels.lean:66
def filler ... : VarietyWithModels D jC where
  shv := provisionalShimX D.what₂.Tau (max r 2) 1 lev le_rfl (by omega) hlev
  Mp := fun _ _ _ => Unit
  CurveM := fun _ _ _ _ => Empty
  degM := fun _ _ _ _ _ _ => 0
  htMdl := fun _ _ _ => ()
  htCurve_deg := fun _ _ c => Empty.elim c
```

`smallShim` 被 `provisionalDivX` 用作 `shv`（该除子的 Shimura 数据），`provisionalDivX` 又是 `exists_provisionalDivX` 的构造项；后者被 `ExistsStagesClauses.lean:455`、`ExistsEigenReadThirdLocal.lean:26`、`IndexZeroOffTwistedPlaces.lean:30`、`IndicesPairingLengthsVanishOffTwistedPlaces.lean:471` 用来生产"读数/阶段"所需的除子。`filler` 则通过 `atSpace` 在"没有对应数据"时兜底返回一个 `VarietyWithModels`。

于是：**整条算术侧流水线的具体对象，是一个只有一个分量、一条线丛、零曲线、零度数、零曲率的模型；它的三个正性谓词是恒真。**

### 4.4 正性为何是这条策略最硬的地方，以及它如何被免掉

`Definitions\Divisors\SlopeTestRemainingChoices.lean` 定义了喂给"墙小性"（wall smallness）机器的输入组：

```lean
-- :96
def Positive : Prop := ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ),
  IsRat Y u → supAbs Y u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ → Dominant Y (A.sh u s) → NefCond Y B (A.sh u s) →
  Y.semipos (Y.Mbar B u s) ∧ Y.nefFib (Y.Mbar B u s)

-- :100
def Squeeze : Prop := ∀ L : Y.ALB, Y.semipos L → Y.nefFib L → ∀ (c : Y.Comp) (e : ℝ),
  ((∀ y, Y.compPt y = c → e ≤ A.ht L y) → ((dimY Y : ℝ) + 1) * e * Y.geoC L c ≤ Y.arSelfC L c) ∧
  ((∃ Z, A.dense c Z ∧ ∀ y ∈ Z, A.ht L y ≤ e) → Y.arSelfC L c ≤ ((dimY Y : ℝ) + 1) * e * Y.geoC L c)

-- :138
def Inputs (r Cf : ℝ) : Prop :=
  LimFam Φ ∧ PolySize A Φ ∧ Agree A ∧ Positive A ∧ Squeeze A ∧ Heights A ∧ Degrees A ∧ EqVol A ∧
  Antisym Φ hh ∧ FlagHt ... ∧ Relabel Φ ∧ FlatVal A Φ ∧ FlatBd Y Cf ∧ TestVal Φ hh r
```

`Positive` 的内容正是**半正性与纤维 nef 性**：Mbar 点处的算术线丛的半正性（Bost 型比较定理）、其在纤维上的 nef 性。这是 Gillet–Soulé / Bost–Künnemann 理论的结论，也是整个策略中真正困难的分析输入之一。`Squeeze`、`Degrees`、`FlatVal` 都以它为前提。

现在把 `Y := provisionalShimX ...` 代入：

- `Y.ALB = Unit`，故 `∀ L : Y.ALB` 只量化到一个点；
- `Y.semipos L = True`，`Y.nefFib L = True`，两个前提**永远成立**；
- `Y.geoC L c = 0`、`Y.arSelfC L c = 0`，故 `Squeeze` 的内容退化为 `0 ≤ 0`；
- `Y.Comp = Unit`，`Y.vol = 0`，`Degrees` 中的 `0 < A.w c` 与 `Σ w c = 0` 只能靠 `SlopeTestRemainingChoices` 自身的字段凑。

也就是说，**`Positive` 对一个零曲率、零度数的退化模型"成立"，而这个成立不包含任何关于真实 CM Shimura 簇的半正性信息。** 以后任何以 `Positive A` 或 `Squeeze A` 为前提的定理（例如 `WallSmallnessOfDegreesStatement.lean:8` 的 `_root_.GlobalTheory.T.wall_smallness_of_degrees`），在这个实例上得到的结论，讨论的是一个不存在的对象的墙小性。

### 4.5 这一节的结论

`semipos := fun _ => True` 这一行，把"半正性"从一个**需要证明的分析定理**，变成了一个**定义即真的字段**。这不是"用了 `True` 作为占位符以便日后填写"——占位符若未被使用是无害的；而这里的字段被 `Positive`、`Squeeze`、`EqOfSpecializesOfFinite.lean:310,318,331,394`、`FirstChernLeviEqConstant.lean:274,282`、`SemiposAtOfPositive.lean:159,163` 等**大量定理当作实质前提消费**。一个恒真的前提，使这些定理全部退化为"关于 `True` 的真命题"。

---

## 5. 机制三：文献定理槽位由 `trivial` 填充

### 5.1 三条引文

```lean
-- Definitions\ThetaCorrespondence\...\LocalTypeDictionary\DiscreteSpectrumResidualClassification.lean:7
abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True

-- ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:505
theorem UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole
    (O : _root_.UpperTheory.LiteratureTheorems.OpenLiteratureStatements) :
    GlobalTheory.Published.UnusedSlot72 := trivial

-- ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:718（被塞进 O 的字段字面量）
  siegelEisensteinSimplePole := (_root_.UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole O)
```

一个**以 Siegel–Eisenstein 单极点命名**的"文献定理"，其类型是 `UnusedSlot72`，其定义是 `True`，其证明是 `trivial`。

### 5.2 真实命题长什么样

同名的真实命题存在于 `PublishedTheorems\SiegelWeil₂\SiegelEisensteinSimplePoleOfDoublingMethod.lean:14–19`：

```lean
def SiegelEisensteinSimplePole : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa ... → ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : ...), φ ∈ degPS V a μ s₁ → V.rank < b →
    EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1
```

这才是 Siegel–Eisenstein 级数的单极点定理（对 $b > \dim V$ 时 Eisenstein 级数在 $\frac{b-\dim V}{2}$ 处的极点位置与阶数的控制）。它需要 doubling method、Eisenstein 级数的解析性质、以及 Godement–Jacquet 型的局部理论。

仓库有一份真实的陈述，也有一个用 `unfold/exact` 或深层引理去做它的文件；但在 `EveryCharacterOfLiteratureOfVWin` 这个**真正被最终定理消费的 bundle** 里，同名槽位被换成了 `UnusedSlot72 = True`。Sibling 造假点还有 `BernsteinUnitaryProductIrreducibleBis.lean:198`、`BernsteinUnitaryProductIrreducibleTer.lean:64`、`GeometricLemma.lean:73`、`BernsteinUnitaryProductIrreducible.lean:74`——同一手法的复制。

### 5.3 结构体字段充当"文献前提"

`OpenLiteratureStatements`（`EveryCharacterOfLiteratureOfVWin.lean:215–218`）只有三个字段：

```lean
structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where
  caraianiLocalGlobalDual          : _root_.UpperTheory.One.M.Row
  localLanglandsExists             : _root_.UpperTheory.Zero.LLC.RecTExists
  galoisRepOfPolarizedPairLit      : _root_.UpperTheory.One.M.Row
```

其中 `One.M.Row` 与 `Row0b recT` 字面同义（`SatakeParameters\RecT.lean:6`），`RecTExists` 是仓库里少数**真证**的关于局部 Langlands 的存在性定理。也就是说，"文献前提"这个 bundle 实际上就是"`Row0b` 两次 + 一个真定理"。文件里另有约 100 个 `UpperTheory.LiteratureTheorems.*` 声明、58 个 `_of_literature` 与 176 个 `_of_open`，绝大多数**根本不使用** `O`（例如 `:295–296` 的 `chevalley_units_of_literature ... := (GlobalTheory.Published.chevalleyUnits')`）。真正消费 `O` 的只有 `:283–284`（`O.localLanglandsExists`）与 `:285–286`（`O.galoisRepOfPolarizedPairLit`）。

于是"文献定理被形式化"这一说法，在数学上是假的：**一部分槽位由恒真类型填充，大部分槽位悬空，真正承重的仍是 `Row0b`。**

---

## 6. 机制四：恒真条件族与真空参数

除上述三处主装置外，仓库还系统性地使用一组"占位谓词"。全部逐行核对：

| 位置 | 定义 |
|---|---|
| `Definitions\LatticeFrames\IsScaleWithBoundedGamma.lean:14` | `def TrueF (D : D7) : Prop := ...`（配合 `:28 def CanE ... := TrueF D ∧ BigGap D`） |
| `Definitions\LatticeFrames\NotInhAbsOfGamLe.lean:36` | `def TrivialRankCondition (_D : D7) (_L _C' : ℝ) : Prop := True` |
| `Proofs\DivisorProofs\SecondInclusionProjection.lean:100` | `def trivialCondition (M : ℕ) : ∀ {B} [CommRing B], (Fin M → B) → Prop := fun _ => True` |
| `BlockTheory\HeightDefect\OrderValuation.lean:14` | `def trivialClassCondition ... : Prop := True` |
| `BlockTheory\TwistedDiscreteSeries\HeckeValueIntegrality.lean:36` | `def trivialClassCondition : PtClass Xo c := fun _ _ _ => True` |
| `Definitions\Divisors\TwistedPlaceChoiceLiesOverPair.lean:133` | `def trivialTieCondition : TieT := fun _ _ _ => True` |
| `Proofs\HomogeneousIdeals\HasChartsOfForallIsAffineOpen.lean:146` | `abbrev AlgClass.noCondition (k) : AlgClass k := fun _ _ _ => True` |
| `SatakeParameters\SwOn.lean:5` | `def UpperTheory.One.M.TrivialCondition : Prop := True` |
| `Definitions\AutomorphicMembership\ExistsSStageUnconditional.lean:162–165` | `isId / inS / relevant / FeqF := fun _ => True` |
| `Definitions\GaloisGeometry\JointCmpEmbeddingYAlt.lean:37`、`MemberChainFormsLevelPrimeEqMember.lean:232,253` | `okW := fun _ => True` |
| `Definitions\GaloisGeometry\NotIsobaricRigid.lean:89` | `csd := fun _ => True` |
| `Proofs\IwasawaDecomposition\ExistsPadicPackage.lean:33` | `levIn := fun _ => True` |
| `Proofs\IwasawaDecomposition\GoodTupleConditionOfIdempotentZero.lean:398–399` | `mono0 / unr := fun _ => True` |
| `Proofs\IwasawaDecomposition\NotForallNonemptyLocP.lean:240` | `unr := fun _ _ => True` |

`TrivialCondition` 在 12 处被当作**未被使用**的哑元假设出现（`ExistsCgTrueCharSide.lean:61,65`、`GoodAUIso.lean:47`、`MvAll.lean:15`、`Narrow.lean:18`、`AHodgeDgalHodgeOfCgTrueG.lean:30`、`MMvDmvAll.lean:16`、`MMvDmvCg.lean:19`、`MMvDstA.lean:19`、`MNarrow.lean:16`、`SepConjG.lean:22`、`UnitaryReadTrue.lean:20`），即"加一个恒真的假设让它看起来像有前提"。

反向的一手同样存在：`SwOn.lean:3` 定义了

```lean
def UpperTheory.One.M.Sw : Prop := False
```

`Sw` 被用作**惰性参数**：`IsPotCrysAtOfMono0G.lean:119` 的 `galHodge_of_cgTrue_g (sw : One.M.Sw) ...` 与 `:263` 的 `example (sw : One.M.Sw) : type_of% @galHodge_of_cgTrue_alt := @galHodge_of_cgTrue_g sw`，`SepConjG.lean:14,70` 同构。由于 `Sw = False`，`(sw : Sw)` 这个参数在任何非空语境下都无法被提供——它的存在只为让两份签名"看起来相同"，而真正的消费点（`IsPotCrysAtOfMono0.lean:415`）走的是没有 `sw` 的 `_alt` 版本。**真空参数与恒真前提是同一枚硬币的两面：一面让条件永真，一面让条件永假，两种情况下定理都没有增加内容。**

---

## 7. 机制五：把"组装"写成"证明"

结构体打包（pack/unpack）模式在仓库里被大量用来制造"某某成立"的外观。逐行核对三例：

**7.1 `Steps`：17 个字段的重新装填。** `GeometricFlagBases\MapInvMul.lean:19–36` 定义 17 字段的 `Steps`；`:43–87` 的 `Pack.rep` 把 17 个字段卸下来再装回去（唯一实质辅助是 `:38–41` 的 `map_inv_mul`）；`:89` 的 `geoOne_of (h : Steps) (hP : PackEx) : GeoOne`。`StepsMain.lean:17–19` 的 `steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps := ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf, TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩`——17 个槽位中 3 个来自传入假设，其余 14 个是外部 `*_holds` 定理。所以 `Steps` 成立等价于那 14 个定理成立；**`Steps` 本身不增加内容，只是一个中转站**。

**7.2 `GoodK`：全库只有一个构造点。** `ThetaParseval\HalfIndexLattices\SplitStab.lean:18–24` 定义 6 字段的 `GoodK`（`cm/galois/unram/std/inert/psiP`）。全库 336 处引用、跨 270 个文件，但**没有任何一处以 `GoodK` 为结论**；唯一构造点是 `TwoUpOKOfSteps.lean:16`，位于 `twoUpOK_of_steps :13–31` 之内，且自己还要 `hT : TLiftK`。所谓"消去 `GoodK`"，实际是把这个 record 的前提原样搬进来。

**7.3 `InertOK`：只在一个手工造出来的扩域上被证过。** `ThetaParseval\AllCoreOf.lean:12–16`：

```lean
def InertOK (E) : Prop := ∀ w, ¬ IsSplitAt w →
  ((2:𝓞 F) ∉ (w.under).asIdeal ∧ 3 < Ideal.absNorm (w.under).asIdeal ∧ ¬ differentIdeal ℤ (𝓞 F) ≤ (w.under).asIdeal)
```

全库 8 处、5 个文件，**全部是假设或合取项**，没有任何声明以 `InertOK E` 为结论。唯一的证明针对 `CrystallineDescent\ExistsQuadraticCMExtSplitAt.lean:12` 里手工构造的 `↥Q.K`（`:47` 取 `a := -(p:ℤ)`，`:48–49` 取满足 $x^2=a$ 的 $x$，`:90` 得 $x^2 = -p$，`:103–117` 逐位验证非分歧，`:130–136` 验证 $3<|N v|$，`:137–149` 验证不同理想），结论是 `Quad2Ex`（"存在二次 CM 扩域"）。也就是说，`InertOK` 从未对**任意** CM 域被证明；它只在"为该目的专门造出来的扩域"上证过。对 $\mathbb{Q}(i)$ 它字面为假：$2$ 全分歧，$\mathfrak{p}=(1+i)$ 满足 `¬ IsSplitAt`，但 $(2:\mathbb{Z}) \in (2)$。网络审计提到的 `Field0K`/`Inert0K` 在全库中**不存在**（真实对应物叫 `GlobalTheory.Row9.FieldOK`）。

**7.4 `TLift`：只有条件性证明，且无人消费。** `ThetaParseval\SchurStep.lean:116–127` 定义 `TLift`；全库只有 `:116` 与 `:271` 两处引用。`:270–271` 的 `tLift_of` 带 9 个具名 `Prop` 假设，证明体 272–306 行；**这个定理在任何地方都没有被调用**。准确的说法不是"只有定义、从未证明"，而是"只有条件性证明，且全库无人消费"。

**这一节的共同结构**：把一个复用的数学内容（例如"Kodaira–Spencer 映射是晶体比较"）打包成一个 record 的 17 个字段，然后写 `steps_of` 把外部定理填进去，再写 `geoOne_of` 把 record 换成 `GeoOne`。读者在 `geoOne_holds : GeoOne` 处看到的是一行干净的结论；看到 `GeoOne` 又被递进 `galoisLocalGlobal_of_geometry_lift`；但**没有任何一步真的处理了所命名的数学对象**——那被推给了 14 个外部 `*_holds`，其中一部分再推给 `True`。

---

## 8. 机制六：改名当证明

`GeometricFlagBases\WeightOneGeometricRealization.lean` 全文 13 行：

```lean
theorem weight_one_geometric_realization : LocalSmoothExtension.HolomorphicLefschetzFormula := by
  unfold LocalSmoothExtension.HolomorphicLefschetzFormula
  exact GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence

theorem geoOne_holds : GeoOne :=
  geometric_realization_of_weight_one weight_one_geometric_realization
```

`unfold` 把目标展开成 `HolomorphicLefschetzFormula` 的定义体，`exact` 直接引用一条**类型逐字相同**的定理。这不是证明，是改名。同样的三段逐字重复出现在：

- `LefschetzSigmaSums\HodgeTraceFromLefschetzAndGroupSide.lean:102–111`（`def HolomorphicLefschetzFormula`）；
- `Proofs\SatakeParameters\LefschetzFixedPointFiniteEtaleCorrespondence.lean:8–15`（证明体是 `first | exact @UpperTheory.Cb.... | exact ...`）；
- `EtaleClopenDescent\LefschetzFixedPointFiniteEtaleCorrespondence.lean:255–262`。

必须说清的一点：这条链的**最底端**是有实质数学的。`EtaleClopenDescent\HolomorphicLefschetzFiniteEtaleIntegral.lean` 共 245 行，`:74` 起是约 170 行的证明，调用了 5 条确实证明过的 `etaleCorrespondence_*_statement`（`CommutativeAlgebra\EtaleCorrespondenceSectionsStatement.lean:51–69` 等）。所以此处的问题不是"底端为空"，而是：**底端的实质工作被上面两层逐字复制的"改名"包装成了"权重一的几何实现"，而 `geoOne_holds` 又只用到这个包装。** 网络审计说底端是"约 370 行、自己证自己"，行数不对（245 行），"自己证自己"也不准确；准确的说法是"三层同义反复，中间两层是搬运"。

---

## 9. 数学上的不成立在哪里

把上面六节拼起来，可以给出本报告的正式论证。

### 9.1 命题 **P**：该仓库证明了 RH

任何一份形式化证明要成立，需要同时满足两个条件：

- **(C1) 形式条件**：其证明项在类型论意义上使目标类型有居留（inhabited）。
- **(C2) 语义条件**：证明项所用的每一个中间陈述，其**定义体**表达的是它名字所声称的数学内容。

全库扫描表明 (C1) 的问题不在逃逸舱口（§1.2 全为零），而在于——本副本从未编译（§1.3），故 (C1) 本身尚未被验证；但本报告不需要它。

本报告攻击的是 **(C2)**，且 (C2) 的失败与编译无关：

1. **几何层**：`GeoP` 是"几何性"的类型；`anyGeometry := fun _ _ _ => True` 使"几何性"退化为恒真（§3）。凡以 `anyGeometry` 为见证处，"这个除子是几何对象的实现"由 `True` 兑现。
2. **分析层**：`ShimX.semipos/nefFib/arNef` 承载半正性与 nef 性；`provisionalShimX` 把它们填成 `fun _ => True`，同时令 `ALB := Unit`、`Comp := Unit`、`CurveHT/DR/FibComp := Empty`、全部陈数与度数为 0（§4）。于是 `Positive`、`Squeeze`、`Degrees` 在该实例上的成立**不含任何半正性信息**。
3. **文献层**：`UnusedSlot72 := True`，`siegel_eisenstein_simple_pole := trivial`（§5）。一条以单极点定理命名的"文献结果"，其证明是一次 `trivial`。
4. **条件层**：`TrivialCondition := True` 被当作哑元前提使用 12 次；`Sw := False` 被当作惰性参数使用（§6）。
5. **组装层**：`Steps`（17 字段）、`GoodK`（唯一构造点）、`InertOK`（只对专造扩域）、`TLift`（无人消费）（§7）；权重一实现是三层改名（§8）。

这五条合起来说明：**从 `Row0b` 到 `RH` 的这条推导，其"几何存在""半正性""文献定理"三类前提，在定义层面已被抽成恒真或退化。** 于是这条链实际证明的命题是：

$$
(\text{Row0b recT}) \;\Longrightarrow\; \text{EveryCharacter} \;\Longrightarrow\; \text{RH}
$$

其中 `Row0b` 本身是未证的强猜想（§2.2），而 `EveryCharacter` 与 `RH` 之间的那一步虽然为真（§2.2），却只是"若所有 Dirichlet L 函数在右半平面非零，则 RH"——这一步的正确性不补偿它前一步的空洞。

**必须正面回答的一个反驳。** 有人会说：`Row0b recT` 明明有一个闭合的证明项（`Development.lean:27–31`），若这份开发真能编译，RH 就被证明了；所以"定义体被抽空"只是命名口味问题，不构成对证明的反驳。

这个反驳有一半是对的，所以要把两种情形分开说清：

- **情形 A（本副本的实际状态）：不能编译。** 从未构建，`.lake` 下只有 `packages`，连 `Main.olean` 都不存在（§1.3）。此种情形下不存在"证明"，只有源码。这是最可能的情形，也是作者 README 自己承认的边界。
- **情形 B：某天完整 `lake build` 成功。** 那么这份开发就是一份真的 RH 形式化证明，本报告第 1 条理由当日作废，作者应当得到数学界最高规格的审查——这是 §10.4 的证伪条件。

本报告的判决不属于 A 或 B 中的任何"数学真假"，而是一个语义门槛问题：一份证明若要被采信，其每一处中间陈述的定义体必须表达它名字所指的数学内容。当 `anyGeometry`、`semipos`、`UnusedSlot72` 被写成 `True`，而调用方以为自己用的是几何存在性、半正性与单极点定理时，**被检查的命题已经与数学家所讨论的命题不是同一个**（(C2) 失败）。因此准确的判决是：这份产物即使将来编译通过，也不能被当作 RH 的证明采信，除非 §10.4 所列三处中有真实的构造被找到。**"有没有项"与"项证的是什么"是两件事，本报告只就后者下判断。**

### 9.2 一个思想实验：把 `True` 换回去

判断"写死恒真"是否致命，最直接的方法是**把恒真的部分换回真实内容，看链条是否还站得住**：

- 把 `anyGeometry` 换回 `geoOf Q`（`OverIx.lean:16`）：于是 `OAt.geo` 字段要求"存在 $c>0$ 使 $X$ 是 $Q$ 的几何实现且落在真曲面上"。仓库**没有任何一处**给出这样的 $c$ 与实现关系——`IsGeoOf` 的证明在全库中从未针对具体对象被构造过（这正是"几何实现"需要真数学的地方）。
- 把 `semipos := fun _ => True` 换回真正的半正性：需要 Chern 联络曲率的半正定性，即 Bost / Gillet–Soulé 型比较定理。仓库提供的 `connN := 0`、`curvN := 0` 使该对象的曲率为零——**一个曲率处处为零的对象，其半正性是平凡的，但它不是任何真实 Shimura 簇的 Hodge 丛。**
- 把 `UnusedSlot72` 换回 `SiegelEisensteinSimplePole`（真实定义见 §5.2）：需要 doubling method 与 Eisenstein 级数解析理论，仓库在该槽位没有证明。
- 把 `TLift` 的一般版换回被使用的条件：`tLift_of` 的 9 个假设无一被满足，该定理无人调用。

四处替换之后，链条立即断裂。**这证明"写死恒真"不是无关紧要的工程便利，而是这条链能否成立的全部内容所在。**

### 9.3 一个必须说清的区分

有人会把本报告读成"你在说 RH 是假的"。本报告不主张这一点，也不主张作者在造假。本报告主张的是：

> **形式产物的存在，不等于数学命题的证明。** 当证明的中间陈述被写成 `True`、退化见证与 `trivial` 时，Lean 所检查的命题已经不是数学家所讨论的命题；此时"编译通过"至多证明"从恒真前提可以推出 RH"，这在一阶逻辑中是真命题，却与"RH 被证明"毫无关系——正如"若 $1=0$ 则 RH"为真，不构成 RH 的证明。

---

## 10. 本报告的边界、反方与可反驳条件

一份只有指控没有边界的审计报告是不可信的。以下逐条列出我核到的、**对作者有利**的事实。

### 10.1 我确认是真的部分

| 项目 | 结论 |
|---|---|
| 顶层陈述 | `Main.lean:4` 使用的是 Mathlib 的真 `RiemannHypothesis`，无遮蔽 |
| `EveryCharacter ⇒ RH` 归约 | 真证明（`RhOfRight.lean:5–62`、`CritLine.lean:29–32`），用了函数方程与 Γ 因子非零 |
| `recTExists` | 真定理（`LocalLanglands\LocalCentralUnits\RecTExists.lean:20–66`），构造了 12 字段的 `LawsT` |
| `tLift_of_k` | 40 行真证明（`GalTPDefs.lean:141–177`） |
| 全纯 Lefschetz 底端 | 245 行文件、约 170 行证明，调用 5 条真定理（§8） |
| 逃逸舱口 | `sorry`/`axiom`/`native_decide`/`unsafe` 全为 0；唯一 `addDecl` 是内核校验的重命名拷贝 |
| 规模与哈希 | 175,187 文件、909,822 行 import、SHA-256 与 README 一致 |

### 10.2 我修正的网络审计错误

| 网络说法 | 审计结论 |
|---|---|
| `KSA11` 结构 | 全库不存在；真实名是 `KSAll`（`PackExOf.lean:93`） |
| `Field0K` / `Inert0K` | 全库不存在；真实对应物是 `GlobalTheory.Row9.FieldOK` |
| "唯一保证 `SatU` 非空的引理 `SphOffU` 只在 split 位给出，故 inert 位条件为空 → 空真" | **攻点落空**。`VBase` 的量化用的是 `UsPl`（`ApartAllEmpty.lean:24–25`），其定义**第一个合取项就是 `IsSplitAt w`**，所以 inert 位根本不进入 `∀`。这不是"空真"，而是"前提把非 split 位排除了"。另有至少 4 处构造 `∃ B, SatU`（`ExistsTestOp.lean:58–59`、`AutomorphicLevelAwayNonsplit.lean:31–32,47`、`ExistsSatUOfUnderEq.lean:14`、`StConj.lean:47`） |
| "权重一实现底端约 370 行，自己证自己" | 文件 245 行；底端是**真证明**；问题在中间两层的改名（§8） |
| "整体重量压在 `Row0b`，只用了 3 次" | 承重部分成立；"3 次"不成立，全库使用远多于此 |
| "`True` 冒充 Siegel–Eisenstein 单极点定理" | **成立**，但坐标要改正：`EveryCharacterOfLiteratureOfVWin.lean:505–506`，类型是 `UnusedSlot72 : Prop := True`，原型定义在 `PublishedTheorems\SiegelWeil₂\SiegelEisensteinSimplePoleOfDoublingMethod.lean:14–19` |

这些修正不削弱本报告的结论，反而使它更难被一句话驳倒。

### 10.3 为什么"编译错误"不是本报告的论据

用户可以要求"不需要编译错误"，这是对的：若把论证建立在"它编译不过"上，作者只要修好编译，论证就失效。而本报告的论证是**语义的**：即便它编译通过、即便 `lake build` 成功产出 `Main.olean`，只要 `anyGeometry`、`provisionalShimX`、`UnusedSlot72` 仍是今天这个样子，`Main.riemannHypothesis` 的证明项就仍然是从恒真前提出发的推导。**编译成功只能确认 (C1)，不能确认 (C2)。**

### 10.4 可反驳条件（本报告的证伪路径）

本报告的结论会被以下任一事实推翻：

1. 找到一处使用 `OAt (geoOf Q)`（或任何非 `anyGeometry` 的几何谓词）并**实际消费** `IsGeoOf` 字段的地方——即几何实现被真的构造过；
2. 找到一处对真实（非 `provisionalShimX`）的 `Y : ShimX` 证明 `Positive A` 或 `Squeeze A` 的地方——即半正性被真的证明过；
3. 找到 `Row0b recT` 的真正证明（而非 `Development.lean:27–31` 那样的项构造）；
4. 指出本报告任何一条引文与源码不符。

若 1–3 中任一条成立，本报告相应章节应立即作废。我逐行核对过现有源码，未见这样的证据。

---

## 11. 结论

回到最初的问题：**"该仓库证明了黎曼猜想吗？"**

**没有。** 两条独立的理由：

1. **承重命题未证（就其数学内容而言）。** 全部文件收敛到 `Row0b recT`——Fontaine–Mazur 型局部-整体 Langlands 的全称断言，一个强于 RH 的未解猜想。仓库确实写出了它的一个证明项，但该证明项沿 `GeoOne → weight-one 实现 → True` 一路穿过 §3–§8 的全部空洞；把问题搬到更强的地方并称之为证明，不构成证明。
2. **关键条件写死恒真。** 承载数学内容的三个输入层被替换为：
   - `anyGeometry := fun _ _ _ => True`（几何存在性，`OverIx.lean:19`）；
   - `provisionalShimX`：`Comp := Unit`、`CurveHT/DR/FibComp := Empty`、`vol/chern/deg := 0`、`semipos/nefFib/arNef := fun _ => True`（半正性与 nef 性，`ExistsProvisionalShimX.lean:13–68`）；
   - `UnusedSlot72 := True` 与 `siegel_eisenstein_simple_pole := trivial`（文献定理，`EveryCharacterOfLiteratureOfVWin.lean:505–506`）。

三分之二的"文献定理"槽位悬空，四类强条件被 `True`/`False` 占位，几何与分析输入由退化模型兑现。具体到文献层：`OpenLiteratureStatements` 的三个字段（`EveryCharacterOfLiteratureOfVWin.lean:215–218`）是两个同一个 `One.M.Row` 命题加一个 `RecTExists`，没有一个来自文献；58 条 `_of_literature` 中绝大多数证明体完全不使用 `O`（如 `:295–296` 直接落回 `GlobalTheory.Published`），真正消费 `O` 的只有 `:283–284` 与 `:285–286` 两处。于是这份产物的数学地位是：**一个从恒真前提与未证猜想出发、形式地推出 Mathlib 版 RH 的推导**。它在类型论上或许有居留（未编译，不能确认）；在数学上，它不是 RH 的证明。

对读者的建议只有一句：**不要看 `Main.lean` 那一行 `:= rhOfAll`，去看 `Row0b`、看 `semipos`、看 `UnusedSlot72`——证明的分量在前提里，不在结论的写法里。**

---

## 附录 A：核心证据表

| 编号 | 文件:行 | 内容 | 数学含义 | 证据等级 |
|---|---|---|---|---|
| A1 | `src\Main.lean:4` | `theorem riemannHypothesis : RiemannHypothesis := rhOfAll` | 顶层陈述，用真 Mathlib RH | 逐行核对 |
| A2 | `Formalism\GammaFactorNonvanishing\RhOfRight.lean:5` | `rh_of_right (hz : ∀ s, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis` | 归约为右半平面非零，真证明 | 逐行核对 |
| A3 | `TypeConditions\WeightsConjBis.lean:69–73` | `def Row0b : Prop := ∀ (E Ω) ... ∃ r wt HT, PropsB ...` | 未证的强猜想 | 逐行核对 |
| A4 | `CharacterBoxes\MainConclusion.lean:7–8` | `everyCharacter_of_row (Row0b recT)` + 三字段 bundle | 承重点 | 逐行核对 |
| A5 | `AutomorphicMembership\OverIx.lean:19` | `def anyGeometry : GeoP := fun _ _ _ => True` | 几何谓词恒真 | 逐行核对 |
| A6 | `AutomorphicMembership\OverIx.lean:44–49` | `OAt.geo : Γ ...`；`OX Γ` | 恒真谓词作几何见证 | 逐行核对 |
| A7 | `AutomorphicMembership\NotGeoClFalse.lean:21–28` | `inductive GeoCl` / `geoCl` | 恒真沿基变换传播 | 逐行核对 |
| A8 | `Formalism\LocalRingCardinality\DataDIV.lean:236–238` | `semipos / nefFib / arNef : ALB → Prop` | 正性字段 | 逐行核对 |
| A9 | `Proofs\FoundationProofs\ExistsProvisionalShimX.lean:13–68` | `provisionalShimX`：`Unit/Empty/0` + 三正性 `fun _ => True` | 退化见证 | 逐行核对 |
| A10 | `Proofs\FoundationProofs\ExistsProvisionalDivX.lean:213,221,296` | `smallShim` / `shv` / `exists_provisionalDivX` | 退化见证被使用 | 逐行核对 |
| A11 | `Proofs\IwasawaDecomposition\VarietyWithModels.lean:66` | `filler ... shv := provisionalShimX ...` | 同上 | 逐行核对 |
| A12 | `Definitions\Divisors\SlopeTestRemainingChoices.lean:96–98,100–102,138–140` | `Positive` / `Squeeze` / `Inputs` | 正性条件的消费点 | 逐行核对 |
| A13 | `ThirdPlaceSeries\EveryCharacterOfLiteratureOfVWin.lean:505–506,718` | `siegel_eisenstein_simple_pole ... := trivial` | 文献定理由 `trivial` 填充 | 逐行核对 |
| A14 | `Definitions\...\DiscreteSpectrumResidualClassification.lean:7` | `UnusedSlot72 : Prop := True` | 槽位类型恒真 | 逐行核对 |
| A15 | `PublishedTheorems\SiegelWeil₂\SiegelEisensteinSimplePoleOfDoublingMethod.lean:14–19` | `SiegelEisensteinSimplePole` 真定义 | 被绕过的真实命题 | 逐行核对 |
| A16 | `SatakeParameters\SwOn.lean:3,5` | `Sw := False`；`TrivialCondition := True` | 真空参数 + 恒真前提 | 逐行核对 |
| A17 | `GeometricFlagBases\MapInvMul.lean:19–36,43–87,89` | `Steps` 17 字段 / `Pack.rep` / `geoOne_of` | 组装当证明 | 逐行核对 |
| A18 | `ThetaParseval\HalfIndexLattices\SplitStab.lean:18–24` + `TwoUpOKOfSteps.lean:16` | `GoodK` 唯一构造点 | 组装当证明 | 子审计核对 |
| A19 | `ThetaParseval\AllCoreOf.lean:12–16` + `CrystallineDescent\ExistsQuadraticCMExtSplitAt.lean:12` | `InertOK` 只对专造扩域证 | 一般情形未证 | 子审计核对 |
| A20 | `ThetaParseval\SchurStep.lean:116–127,270–306` | `TLift` / `tLift_of`（9 假设，无人调用） | 一般版无消费 | 子审计核对 |
| A21 | `GeometricFlagBases\WeightOneGeometricRealization.lean:7–11` | `unfold ...; exact ...` | 改名当证明 | 逐行核对 |
| A22 | `EtaleClopenDescent\HolomorphicLefschetzFiniteEtaleIntegral.lean:74–245` | 170 行真证明 | 底端有实质数学 | 子审计核对 |

## 附录 B：术语对照

- **`GeoP`**：几何谓词类型，`∀ D, Pj.Core D → DivX D → Prop`，即"这个除子具备几何性"的断言。
- **`ShimX`**：约 65 字段的结构体，描述 Shimura 型对象的算术几何数据（分量、曲线、陈数、算术度、正性等）。
- **`Row0b`**：Fontaine–Mazur 型局部-整体 Langlands 对应的全称版本；RH 由它推出，但它不被 RH 推出。
- **`semipos / nefFib / arNef`**：Hermitian 线丛半正性、纤维 nef 性、算术 nef 性——本策略中最硬的分析输入。
- **"写死恒真"**：把承载数学内容的 `Prop` 字段/谓词定义为 `True`（或 `fun _ => True`），使依赖它的定理在定义层面即被满足。

---

*本报告的全部引文均取自 `D:\LiManCX\lean\src` 的实际源码行；引文行号已按文件实际行号核对。报告不对"RH 是否为真"作任何断言。*
