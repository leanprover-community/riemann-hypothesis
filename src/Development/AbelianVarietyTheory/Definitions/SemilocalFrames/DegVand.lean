module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

variable (D : D7) (large₂ : SizeData₂ D)

def HypZ (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def MomIn (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (a : Fin (D.R.rS + 1)) (q : ℕ), (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
        ∫⁻ x, ENNReal.ofReal (lA D.R.k D.R.rS W.z (Matrix.of x) a ^ (2 * q)) *
            (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
          ENNReal.ofReal (large₂.sc.b ^ (2 * C * D.R.m * q)) * l2SG W.νS A.Φ

def SchurSt (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        MMv D w w' A μsec ≤
          ENNReal.ofReal ((Tr D w * Tr D w') ^ (D.R.k - 1) *
            ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ) * volUn D.R.r * volUn (D.R.k - 1) /
              (A.deg * volUn D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k))) *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def ABSr (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        DminN W.z W.z' γ D.R.rS ≠ 0 →
          Integrable (fun x => (innerSL ℂ (S.Φ' (Matrix.of x))).smulRight (S.Φ (γ * Matrix.of x))) νR ∧
          ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
            (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
            (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def LocIn (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ W, HypTT D w w' → GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    MultOne W.z (psiS D W.z) A.σ W.π ∧ MultOne W.z' (psiS D W.z') A.σ W.π' ∧
      Decay A.σ (DD A.σ A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5)

def Big (Cl m₀ : ℝ) : Prop := D.host.rdE ≤ large₂.sc.b ∧ 1 ≤ Cl * D.R.m ∧ m₀ ≤ D.R.m

def BSch (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

def Sizes (Cl Cg CT : ℝ) : Prop :=
  1 < large₂.sc.L ∧ Real.log large₂.sc.b = large₂.sc.L ∧ Real.exp 1 < large₂.sc.b ∧ D.R.m = 2 * D.R.rS + 2 ∧
    D.R.r = 2 * D.R.rS + D.R.k + 1 ∧ Fintype.card D.what₂.Tau = D.R.f ∧ Cl ≤ D.R.m ∧ D.R.m ^ 4 ≤ D.R.k ∧
    1 ≤ D.host.v ∧ D.host.rdE = 2 * D.host.v ∧ D.host.ka = Real.pi / D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧
    1 ≤ gg D ∧ gg D ≤ large₂.sc.b ^ (2 * Cg) ∧ 8 ≤ Cg ∧ (D.R.k : ℝ) ≤ large₂.sc.b ^ Cg ∧
    (∀ w, Tr D w ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) ∧ (∀ w τ, 0 < Formalism.MainNotions.S.vand (uS D w τ) ∧ 0 < Tcrit D w τ) ∧
    ∀ τ (a c : Fin (2 * D.R.rS + D.R.k + 1)), a < c →
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ a - lamD D τ c

end GlobalTheory.Amp
