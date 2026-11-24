module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem isPsEff_pull_redι_univ_of_hasNonzeroSec_pow :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  intro k _ _ X _ _ hp M hM r hr hs Z hZ
  have hirr : IsIrreducible (Z : Set X) := hZ ▸ IrreducibleSpace.isIrreducible_univ X
  have := isIntegral_red hirr
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
  obtain ⟨x, hx⟩ := (range_redι Z).ge (hZ.ge (Set.mem_univ (genericPoint X)))
  rw [← hx] at hs
  have e := nonzeroLocus_secPull s (redι Z)
  have h1 : HasNonzeroSec ((lbPow M r).pull (redι Z)) :=
    ⟨secPull s (redι Z), sec_ne_zero_of_mem (x := x) (e.ge hs)⟩
  have hM' := LB.isLB_pull hM (redι Z)
  refine isPsEff_of_hasNonzeroSec_pow (hH.pull_of_isClosedImmersion (redι Z)) hM' hr
    (h1.of_cls_eq (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _) ?_)
  exact (cls_eq_iff (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _)).2
    (lbIso_lbPow_pull hM (redι Z) r)

end GlobalTheory
