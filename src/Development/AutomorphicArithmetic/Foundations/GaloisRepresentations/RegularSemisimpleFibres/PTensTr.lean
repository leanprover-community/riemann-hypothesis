module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
