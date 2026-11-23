module

public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem map_eq_prod_of_valuationSubring {O A K F : Type} [CommRing O] [Field K] [CommRing F]
    (B : ValuationSubring K) (j : O →+* K) (φ : B →+* F) (ψ : O →+* F)
    (h : ∀ y, ∃ h : j y ∈ B, φ ⟨_, h⟩ = ψ y) (t : A → K) (ι : A → F)
    (ht : ∀ x, ∃ h : t x ∈ B, ι x = φ ⟨_, h⟩) (p : O[X]) (s : Multiset A)
    (hp : p.map j = (s.map fun x => X - C (t x)).prod) :
    p.map ψ = (s.map fun x => X - C (ι x)).prod := by

  let j' : O →+* B :=
    { toFun := fun y => ⟨j y, (h y).1⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun a b => Subtype.ext (map_mul j a b)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j a b) }
  let t' : A → B := fun x => ⟨t x, (ht x).1⟩
  have hψ : ψ = φ.comp j' := by
    ext y
    exact ((h y).2).symm
  have hj : B.subtype.comp j' = j := by
    ext y
    rfl
  have hB : p.map j' = (s.map fun x => X - C (t' x)).prod := by
    apply Polynomial.map_injective B.subtype Subtype.val_injective
    rw [Polynomial.map_map, hj, hp, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hψ, ← Polynomial.map_map, hB, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [(ht x).2]

end GlobalTheory.TypeLeaf
