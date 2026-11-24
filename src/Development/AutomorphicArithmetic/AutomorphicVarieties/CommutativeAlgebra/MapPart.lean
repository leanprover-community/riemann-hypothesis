module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.map_part :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (W' : WPres O X R'), (∀ s, W'.z s ∈ maximalIdeal R') → ∀ f : R →ₐ[O] R', (∀ s, f (W.z s) ∈ W'.part (W.wt s)) → ∀ j, ∀ x ∈ W.part j, f x ∈ W'.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ W' hW' f hf j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (f.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal R' := fun s => by
    show f (W.z s) ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hW s
  refine part_closed O X R' W' hW' j _ fun N => ⟨_, ?_, GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) hm N g⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [coeff_truncTotal_eq_ite, hg d hne, ite_self]
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded W'.part W.wt (fun s => f (W.z s)) d (fun s _ => hf s)
