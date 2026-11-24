module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar TopologicalSpace

theorem isOpen_of_isClosed_of_generizing {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (S : Set α) (hc : IsClosed S) (hs : ∀ x y : α, x ⤳ y → y ∈ S → x ∈ S) : IsOpen S := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hT : IsClosed (⋃₀ {C ∈ irreducibleComponents α | Disjoint C S}) := by
    rw [Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C (h : C ∈ {C ∈ irreducibleComponents α | Disjoint C S}) => h.1).isClosed_biUnion
      fun C h => isClosed_of_mem_irreducibleComponents C h.1
  have e : Sᶜ = ⋃₀ {C ∈ irreducibleComponents α | Disjoint C S} := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro s hsC hsS
      have hC := isIrreducible_irreducibleComponent (x := x)
      have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
      obtain ⟨c, hcg⟩ := QuasiSober.sober hC hcl
      have hcs : c ∈ S := hs c s (hcg.specializes hsC) hsS
      exact hx (hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hcs) (by
        rw [hcg.def]; exact mem_irreducibleComponent))
    · rintro ⟨C, ⟨-, hd⟩, hx⟩ hxS
      exact Set.disjoint_left.1 hd hx hxS
  rw [← isClosed_compl_iff, e]
  exact hT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genPt_specializes_of_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p y : X}
    (hp : genPt ξ ⤳ p) (hy : y ⤳ p) : genPt ξ ⤳ y := by
  haveI := CptInh.dom ξ h ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := this
  obtain ⟨a, ha⟩ : genPt ξ ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨b, hb⟩ : y ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  let o : Spec (CommRingCat.of (X.presheaf.stalk p)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))
  have hoc : ∀ c : Spec (CommRingCat.of (X.presheaf.stalk p)), o ⤳ c := fun c =>
    (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) c).1 bot_le
  have h1 : X.fromSpecStalk p o ⤳ genPt ξ := by
    rw [← ha]; exact (hoc a).map (X.fromSpecStalk p).continuous
  have h2 : X.fromSpecStalk p o ⤳ y := by
    rw [← hb]; exact (hoc b).map (X.fromSpecStalk p).continuous
  rwa [CptInh.nogen ξ h _ h1] at h2

theorem isOpen_closure_genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsOpen (closure {genPt ξ}) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨W, hpW⟩ : ∃ W : X.affineOpens, p ∈ W.1 := by
    obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hpW⟩
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  haveI : NoetherianSpace (W.1 : X.Opens) := noetherianSpace_of_isAffineOpen W.1 W.2
  haveI : QuasiSober (W.1 : X.Opens) := inferInstanceAs (QuasiSober (W.1 : X.Opens).toScheme)
  have ho : IsOpen (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)) :=
    isOpen_of_isClosed_of_generizing _ (isClosed_closure.preimage continuous_subtype_val)
      fun x y hxy hy => by
        have hy' : genPt ξ ⤳ y.1 := specializes_iff_mem_closure.2 hy
        exact specializes_iff_mem_closure.1
          (genPt_specializes_of_specializes ξ h hy' (hxy.map continuous_subtype_val))
  refine ⟨Subtype.val '' (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)), ?_,
    W.1.isOpen.isOpenMap_subtype_val _ ho, ⟨⟨p, hpW⟩, hp, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem cpt_open_integral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → ∃ U : X.Opens, (∀ q : X, q ∈ U ↔ genPt ξ ⤳ q) ∧
      IsClosed (U : Set X) ∧ IsIntegral U.toScheme := by
  intro X Ω _ ξ _ h
  let U : X.Opens := ⟨closure {genPt ξ}, isOpen_closure_genPt ξ h⟩
  have hU : ∀ q : X, q ∈ U ↔ genPt ξ ⤳ q := fun q => specializes_iff_mem_closure.symm
  refine ⟨U, hU, isClosed_closure, ?_⟩
  haveI : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := genPt ξ)).closure
  haveI : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
    haveI := CptInh.dom ξ h ⟨U.ι x, (hU _).1 x.2⟩
    have e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.CompanionTheory.Ar.Flat
