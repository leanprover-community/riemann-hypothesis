module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCardStatement
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tmap_injective_card_coker_of_isIsogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧
      Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  intro K _ l _ hl A B f hf
  have hsurj : Function.Surjective (ptMap f) := (surjective_iff_ptMap_surjective K A B f).1 hf.2
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hdiv : ∀ x : A.Pt, ∃ y, y ^ l = x := pt_divisible K A l (Fact.out : l.Prime).ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card l A.Pt B.Pt (ptMap f) hdiv hsurj hfin
  exact ⟨h1, h2.trans (GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree K l hl A B f hf)⟩

end GlobalTheory.AV.AbVar
