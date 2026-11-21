import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.KV

open MeasureTheory
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
  Formalism.L2.S.S7.PositiveOrthantChangeOfVariables
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)
open PI.IwaMeasEx.Sk

structure admitted {X : CData} {J : ℕ} (c : Composition J) (D : BaseDatum X.I J) where
  μK : Measure X.I.GA
  μN : Measure X.I.GA
  μM : Measure X.I.GA
  cIw : ℝ≥0∞
  FN : Set X.I.GA
  FM : Set X.I.GA
  Om : Set X.I.GA
  VM : ℝ≥0∞
  hK : PK D μK
  hN : PN D c μN
  hM : PM D c μM
  hI : IntF μK (muP D c μN μM) cIw
  hF : FdP D c μN μM FN FM Om
  hL : LeviP D c μM FM VM

structure Sc where
  s : ℝ≥0∞
  sN : ℝ≥0∞
  sM : ℝ≥0∞
  vU0 : ℝ

abbrev GPred : Type 1 :=
  ∀ (X : CData) (J : ℕ) (c : Composition J) (D : BaseDatum X.I J), admitted c D → Sc → Prop

def n0 (X : CData) (J : ℕ) : ℕ := X.I.n - 2 * J

def volU (i : ℕ) : ℝ := Vsph i * (2 : ℝ) ^ ((i : ℝ) * ((i : ℝ) - 1) / 2)

def cIG (X : CData) (J : ℕ) (c : Composition J) : ℝ :=
  ((2 : ℝ) ^ (-(dimN c.blocksFun (n0 X J) : ℝ) / 2) * (volU (X.I.n - X.qq) * volU X.qq) /
    ((∏ i, volU (c.blocksFun i) * (2 : ℝ) ^ ((c.blocksFun i : ℝ) ^ 2 / 2)) *
      volU (X.I.n - X.qq - J) * volU (X.qq - J))) ^ X.I.f

def nBound (X : CData) (J : ℕ) (c : Composition J) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * (dimN c.blocksFun (n0 X J) : ℝ) / 2)

def glG (X : CData) (j : ℕ) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * (j : ℝ) ^ 2) * cn_res X *
    ∏ l ∈ Finset.Icc 2 j, ‖NumberField.dedekindZeta X.I.E (l : ℂ)‖

def lProd (X : CData) (J : ℕ) : ℝ :=
  ∏ M ∈ Finset.Ioc (n0 X J) X.I.n, Formalism.HermitianLatticesTheory.lValEta X.I.E M

def gRatio (X : CData) (J : ℕ) : ℝ :=
  X.I.rd ^ ((X.I.f : ℝ) * ((X.I.n : ℝ) ^ 2 - (n0 X J : ℝ) ^ 2) / 2) * lProd X J

def StepEx (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ a : admitted c D, ∃ sc : Sc, sc.s ≠ 0 ∧ sc.s ≠ ⊤ ∧ sc.sN ≠ 0 ∧ sc.sN ≠ ⊤ ∧ sc.sM ≠ 0 ∧ sc.sM ≠ ⊤ ∧
      G X J c D a sc

def StepB (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    a.cIw * sc.s = ENNReal.ofReal (cIG X J c) * (sc.sN * sc.sM)

def StepC (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    sc.sN * a.μN a.FN ≤ ENNReal.ofReal (nBound X J c)

def StepD (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    0 < sc.vU0 ∧ sc.sM * a.VM = ENNReal.ofReal ((∏ i, glG X (c.blocksFun i)) * sc.vU0)

def StepE (G : GPred) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J)
    (a : admitted c D) (sc : Sc), G X J c D a sc →
    sc.s * X.I.muA X.μf X.fund = ENNReal.ofReal (sc.vU0 * gRatio X J)

def LPos : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → 0 < lProd X J

def StepF : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ c : Composition J, 0 < lProd X J →
    cIG X J c * nBound X J c * (∏ i, glG X (c.blocksFun i)) ≤
      gRatio X J * Formalism.L2.S.S7.DensityConstant.densityConstant X J c


theorem rd_nonneg (X : CData) : 0 ≤ X.I.rd := by
  unfold AutInst.rd
  exact Real.rpow_nonneg (abs_nonneg _) _


end PI.IwaMeasEx.KV

end
