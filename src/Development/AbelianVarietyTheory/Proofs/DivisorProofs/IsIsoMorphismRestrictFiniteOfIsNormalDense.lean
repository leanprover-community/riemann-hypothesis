module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteBirationalNear

theorem isIso_morphismRestrict_of_isNormal : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  intro S T _ ν _ U V hS hV hU hνU hiso
  have : IsReduced S := by
    haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      have := (hS x).1
      infer_instance
    exact isReduced_of_isReduced_stalk S
  have hloc : ∀ x : V, ∃ W : T.Opens, (x : T) ∈ W ∧ IsIso (ν ∣_ W) := by
    intro x
    have e := (V.stalkIso x).symm.commRingCatIsoToRingEquiv
    have h1 : IsDomain (T.presheaf.stalk (x : T)) := by
      have := (hV x).1
      exact e.toMulEquiv.isDomain _
    have h2 : IsIntegrallyClosed (T.presheaf.stalk (x : T)) := by
      have := (hV x).2
      exact IsIntegrallyClosed.of_equiv e.symm
    exact main S T ν U ‹_› ‹_› hiso hU hνU (x : T) h1 h2
  choose W hxW hW using hloc
  let W' : V → V.toScheme.Opens := fun x => V.ι ⁻¹ᵁ W x
  have hcov : iSup W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxW y⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) W' hcov
    fun x => ?_
  have h1 : IsIso (ν ∣_ W x ∣_ ((W x).ι ⁻¹ᵁ V)) := inferInstance
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν (W x) ((W x).ι ⁻¹ᵁ V))).1 h1
  have e : (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ V) = V.ι ''ᵁ W' x := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν V (W' x))).2
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq ν e)).1 h2)

end GlobalTheory.FiniteBirationalNear
