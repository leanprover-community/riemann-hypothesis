module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegGOfTotal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIrrAndDenseOfIsFdegG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepTensor
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
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem isFdegG_tensor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ)
    (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v)) :
    IsFdegG (muInf B.I) B.σs (∏ v, d v) := by
  have hd : 0 < ∏ v, d v := Finset.prod_pos fun v _ => (hF v).1
  obtain ⟨hi, hs, hdense⟩ := B.tens_spec
  refine isFdegG_of_total B.I.Ginf (muInf B.I) B.Hs B.σs (∏ v, d v) (Set.range B.tens)
    (GlobalTheory.HilbTensorUnitary.isURep_rows B hU) hd hdense ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨x', rfl⟩ _ ⟨y', rfl⟩

  have hfun : (fun g : B.I.Ginf => ⟪B.tens y, B.σs g (B.tens x)⟫_ℂ * star ⟪B.tens y', B.σs g (B.tens x')⟫_ℂ) =
      fun g => ∏ v, (coefOn (B.σ v) (x v) (y v) (g v) * star (coefOn (B.σ v) (x' v) (y' v) (g v))) := by
    funext g
    rw [hs, hs, hi, hi, star_prod, ← Finset.prod_mul_distrib]
    rfl
  have hloc := fun v => (hF v).2 (x v) (y v) (x' v) (y' v)
  rw [hfun]
  unfold muInf
  refine ⟨Integrable.fintype_prod_dep fun v => (hloc v).1, ?_⟩
  refine (integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v g => coefOn (B.σ v) (x v) (y v) g * star (coefOn (B.σ v) (x' v) (y' v) g))).trans ?_
  rw [Finset.prod_congr rfl fun v _ => (hloc v).2, hi, hi, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem tensorRep : TensorRep := by
  intro B d hB
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hB v).2.1.2.2.1
  have hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v) := fun v => (hB v).2.2.2
  have hG := isFdegG_tensor B d hU hF
  obtain ⟨hi, hs, -⟩ := B.tens_spec
  refine ⟨GlobalTheory.HilbTensorUnitary.isURep_rows B hU, (isIrr_and_dense_of_isFdegG _ _ _ _ _ hG).1, hG, ?_, ?_⟩
  ·
    have h1 : ⟪B.tens B.w, B.tens B.w⟫_ℂ = 1 := by
      rw [hi]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [inner_self_eq_norm_sq_to_K, (hB v).2.2.1.1]
      simp
    have h2 : ‖B.tens B.w‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
      simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · intro g
    rw [hs, hi]
    rfl

end GlobalTheory.Dec
