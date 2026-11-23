module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.InvTransport

theorem exists_invFam : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ hDec l _ r hcyc inv
  have hcm : ∀ (A' : ValuationSubring Ω') (x : Ω), E x ∈ A' ↔ x ∈ A'.comap E.toRingHom :=
    fun A' x => Iff.rfl
  let eD : ∀ A' : ValuationSubring Ω',
      Dec (F := F) (A'.comap E.toRingHom) ≃ₜ* Dec (F := F') A' :=
    fun A' => subgroupIso Φ _ _ (hDec _ A' (hcm A'))
  have hc : ∀ (A' : ValuationSubring Ω') (h : Dec (F := F) (A'.comap E.toRingHom))
      (m : ZMod (l ^ r)),
      (muLoc F' l r A') (eD A' h) m = (muLoc F l r (A'.comap E.toRingHom)) h m := by
    intro A' h m
    have h1 : cycMod F' Ω' l r (Φ h.1) = cycMod F Ω l r h.1 := hcyc h.1
    show charRep ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) m =
      charRep ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h m
    have h2 : ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) =
        ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h := h1
    rw [charRep_apply, charRep_apply, h2]
  refine ⟨fun A' => inv (A'.comap E.toRingHom) ∘ₗ
    (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A')).toLinearMap, ?_⟩
  intro A A' hA
  obtain rfl : A = A'.comap E.toRingHom := by
    ext x
    exact (hA x).symm.trans (hcm A' x)
  refine ⟨fun hb => hb.comp (LinearEquiv.bijective _), fun z z' hz => ?_⟩
  show inv (A'.comap E.toRingHom) (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A') (Submodule.Quotient.mk z')) = _
  rw [ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk]
  congr 2
  apply Subtype.ext
  funext p
  exact hz p.1 p.2 (eD A' p.1) (eD A' p.2) rfl rfl

end GlobalTheory.CompanionTheory.PTIso.InvTransport
