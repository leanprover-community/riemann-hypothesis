module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BdGlob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BoundsExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsIwasawaRankBoundOfFerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KerQFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PlacesBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankLocalCocycleSpacesLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.x2 :
    CohomologyHyp → UpperTheory.V.Published.FerreroWashington → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → TameL l T.F → ∃ C : ℕ, ∀ (T' : Tower D) (m : ℕ), T.Le T' → IsLayer l m T.F T'.F →
      ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T'.fr ∅).Bounds a T'.d C := by
  intro P hFW Ω _ _ _ l _ c D T hT _
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  obtain ⟨ho, hc, hl⟩ := kerOverRationals_open_commutator_layer D hD T.F
  obtain ⟨r, hr⟩ := exists_iwasawaRank_bound_of_ferreroWashington hFW Ω l (kerQ D T.F) hD.l_odd ho hc inf_le_right
  have hN : (kerQ D T.F).Normal := ⟨fun x hx g => by
    have h : g * x * g⁻¹ * x⁻¹ ∈ kerQ D T.F := hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
    simpa using mul_mem h hx⟩
  obtain ⟨g, hg⟩ := exists_uniform_bound_ncard_placesDividing Ω l (kerQ D T.F) (prodS D) hN ho (residualKernel_properties D hD T).2.2.2.2.2.2.1.1
  refine ⟨r + 2 + 2 * g, fun T' m _ hm k _ a ha => ?_⟩
  obtain ⟨e, hle⟩ := hl m T'.F hm
  have hg' := hg T'.F hle
  have hK : UpperTheory.V.Two.XRk l 1 T'.Kr r := (residualKernel_properties D hD T').2.2.2.2.2.2.2.2 r (e ▸ hr (m + 1))
  obtain ⟨b1, b2⟩ := rank_localCocycleSpaces_le P D hD T' g hg'
  obtain ⟨b3, b4, b5⟩ := rank_cocycleSpaces_le_of_towerIwasawaRank P D hD T' r g hg' hK
  have ea : a = (Ideal.Quotient.lift (maximalIdeal c.O) a ha : ResidueField c.O →+* k).comp (residue c.O) :=
    RingHom.ext fun _ => rfl
  rw [ea]
  refine cocycleBounds_of_ringHom_comp _ (ResidueField c.O) k _ _ _ _ ⟨b1.trans (by omega), fun w _ => (b3 w).trans (Nat.cast_le.2 (by omega)),
    fun w hw => (b4 w hw).trans (Nat.cast_le.2 (by omega)),
    fun w _ => (b5 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega))),
    fun w _ => (b2 w).trans (add_le_add le_rfl (Nat.cast_le.2 (by omega)))⟩
