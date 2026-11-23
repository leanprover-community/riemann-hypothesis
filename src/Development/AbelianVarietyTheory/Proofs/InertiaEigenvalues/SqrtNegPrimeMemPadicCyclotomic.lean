module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory

theorem sqrt_neg_l_mem_adjoin_roots_of_unity :
    ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) →
      y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  intro l _ h4 y hy
  set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef
  have hχm1 : χ (-1) = -1 := by
    simp [χ, MulChar.ringHomComp_apply, hm1]
  have h2 : (2 : Om l) ≠ 0 := two_ne_zero
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
    apply h2; linear_combination hχm1
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hsq := gaussSum_sq hχ1 hq hψ
  rw [hχm1, ZMod.card] at hsq
  set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg

  have hgK : g ∈ K := by
    rw [hg, gaussSum]
    refine sum_mem fun a _ => mul_mem ?_ ?_
    · rw [hχdef, MulChar.ringHomComp_apply]
      exact intCast_mem K _
    · rw [AddChar.zmodChar_apply]
      refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
      show ζ ^ (l ^ 1) = 1
      rw [pow_one]; exact hζ.pow_eq_one

  have hyg : (y - g) * (y + g) = 0 := by
    linear_combination hy - hsq
  rcases mul_eq_zero.1 hyg with h | h
  · rw [sub_eq_zero.1 h]; exact hgK
  · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem hgK

end GlobalTheory
