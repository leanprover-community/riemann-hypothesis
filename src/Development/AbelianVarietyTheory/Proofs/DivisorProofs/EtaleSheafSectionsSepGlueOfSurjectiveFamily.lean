module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_sep_glue_of_points : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  intro R _ F U ι V j hE hS
  have hcov : Sieve.generate (Presieve.ofArrows V j) ∈ Scheme.etaleTopology U := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun u => ?_, hE⟩
    obtain ⟨i, v, hv⟩ := hS u
    exact ⟨i, v, hv⟩
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property
  have hfor := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hfor
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, ht⟩ := hfor (fun _ => 0) (fun i k => by
      change (F.obj.map (pullback.fst (j i) (j k)).op).hom 0 = (F.obj.map (pullback.snd (j i) (j k)).op).hom 0
      rw [map_zero, map_zero])
    have h0 : (0 : Sec F U) = t := ht 0 (fun i => by
      change (F.obj.map (j i).op).hom 0 = 0
      exact map_zero _)
    exact (ht x hx).trans h0.symm
  · obtain ⟨t, ht, -⟩ := hfor y hy
    exact ⟨t, ht⟩

end GlobalTheory.EtC
