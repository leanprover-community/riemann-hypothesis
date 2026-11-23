module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MapNsmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kill :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ) (z : HZ S (j + 1)), Nat.card S • z = 0 := by
  intro S _ _ j z
  classical
  haveI : Fintype S := Fintype.ofFinite S
  let v : S →₀ ℤ := ∑ s : S, Finsupp.single s 1
  have hv : ∀ g : S, perm S S g v = v := by
    intro g

    simp only [v, map_sum, perm_single]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  let fi : (Rep.trivial ℤ S ℤ).ρ.IntertwiningMap (permRep S S).ρ :=
    ⟨LinearMap.toSpanSingleton ℤ _ v, fun g => by
      apply LinearMap.ext_ring
      simp [Rep.trivial_ρ, permRep, hv]⟩
  let gi : (permRep S S).ρ.IntertwiningMap (Rep.trivial ℤ S ℤ).ρ :=
    ⟨aug S, fun g => by
      apply Finsupp.lhom_ext
      intro x c
      simp [Rep.trivial_ρ, permRep, perm_single, aug_single]⟩
  have hcomp : ∀ a : Rep.trivial ℤ S ℤ,
      (Rep.Hom.hom (Rep.ofHom gi)) ((Rep.Hom.hom (Rep.ofHom fi)) a) = Nat.card S • a := by
    intro a
    change aug S (a • v) = Nat.card S • a

    simp only [v, map_smul, map_sum, aug_single, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    nsmul_eq_mul, Nat.card_eq_fintype_card, mul_one]
    ring
  have hsub : Subsingleton (groupHomology (permRep S S) (j + 1)) := by
    obtain ⟨e⟩ := shapiro S S (1 : S) (j + 1)
    haveI : Subsingleton (MulAction.stabilizer S (1 : S)) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a * 1 = 1 := ha
      have hb' : b * 1 = 1 := hb
      simp only [mul_one] at ha' hb'
      subst ha' hb'
      rfl
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupHomology_succ_of_subsingleton
        (Rep.trivial ℤ (MulAction.stabilizer S (1 : S)) ℤ) j)
    exact e.injective.subsingleton
  exact mapNsmul S (Rep.trivial ℤ S ℤ) (permRep S S) (Rep.ofHom fi) (Rep.ofHom gi) (Nat.card S) (j + 1) hcomp hsub z
