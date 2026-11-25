module

public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module Submodule

noncomputable section

namespace Formalism.F

theorem linearIndependent_coe_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  have hs : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    rw [show (Set.range fun i => (b i : E)) = L.subtype '' Set.range b from Set.range_comp _ _,
      Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range fun i => (b i : E))) := hs.symm ▸ ‹_›
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hd]
  unfold Set.finrank
  rw [hs, Module.finrank_eq_card_basis b]

theorem covol_pos' : CovolPos := by
  intro E _ _ _ L hL
  have := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  exact Real.sqrt_pos.2
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos

theorem discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert Metric.isOpen_ball (x := (0 : span ℤ ({v} : Set E))) (ε := ‖v‖)
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
  refine ⟨fun h => by simpa [h] using hv', fun h => ?_⟩
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.1 hx
  have hn : |(n : ℝ)| < 1 := by
    have : ‖(n : ℝ) • v‖ < ‖v‖ := by simpa [Int.cast_smul_eq_zsmul] using h
    rw [norm_smul, Real.norm_eq_abs] at this
    exact (mul_lt_iff_lt_one_left hv').1 this
  have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hn)
  exact Subtype.ext (by simp [hn0])

theorem covol_basic_properties : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, fun v hv => ?_⟩
  · have : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · have := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) :=
      ((linearIndependent_unique_iff (R := ℝ)).mpr hv).restrict_scalars' ℤ
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) :=
      (Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [Set.range_const]))
    have hb : (fun i => (b i : E)) = fun _ => v := funext fun _ => by simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Formalism.F
