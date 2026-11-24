module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem cont_KR_mul (n : ℕ) (y k1 : GR n) : Continuous (fun k : KR n => y * (k : GR n) * k1) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem cont_KR_mul' (n : ℕ) (k1 : GR n) : Continuous (fun k : KR n => (k : GR n) * k1) :=
  continuous_subtype_val.mul continuous_const

theorem mR_mul {n : ℕ} (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem spherical_section_eq_extension {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g = twistedScalarSection p q e (mR g) := by
  simp only [F0, twistedScalarSection]

theorem inK_mul {n : ℕ} (k : KR n) (k1 : GR n) (hk1 : k1 ∈ KR n) : InK (mR ((k : GR n) * k1)) :=
  (KR n).mul_mem k.2 hk1

theorem continuousOn_twisted_section_compact {n : ℕ} (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (y k1 : GR n) (U : Set ℂ) (κ : KR n → ℂ)
    (hκ : Continuous κ) (C : Set (GR n)) (hC : ∀ k : KR n, y * (k : GR n) * k1 ∈ C)
    (hU2c : ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul n y k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) =
      (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) ∘ (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) hU2c hφ.continuousOn
    (fun yz hyz => ⟨hC yz.1, hyz.2⟩)

theorem contOn_Fid {n : ℕ} (k1 : GR n) (U U1 : Set ℂ) (hUU : U ⊆ U1) (κ : KR n → ℂ) (hκ : Continuous κ)
    (Fid : GR n → ℂ → ℂ) (hFidc : ContinuousOn (fun y : GR n × ℂ => Fid y.1 y.2) (univ ×ˢ U1)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul' n k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => Fid ((yz.1 : GR n) * k1) yz.2) =
      (fun y : GR n × ℂ => Fid y.1 y.2) ∘ (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun y : GR n × ℂ => Fid y.1 y.2) hFidc hφ.continuousOn
    (fun yz hyz => ⟨mem_univ _, hUU hyz.2⟩)

end PositivityTheory.Rg.Sw.AbsSt
