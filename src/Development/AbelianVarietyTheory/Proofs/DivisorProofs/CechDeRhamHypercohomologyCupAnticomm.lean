module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem cupHyp_add_cupHyp_swap : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add (f := _)]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]

end GlobalTheory.AbCoh
