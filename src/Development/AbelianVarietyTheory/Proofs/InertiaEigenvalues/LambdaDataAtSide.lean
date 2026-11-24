module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie GlobalTheory.ToricRational GlobalTheory.ToricDistribution

namespace GlobalTheory.LamTie

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_th_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (hE : ∀ (σ : D.host.E →+* ℂ) (x : D.host.E), ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range)
    {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (hD : IsHostDatum D.host φ s κ 𝔣 χ) (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i)
    (hX : ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (χ.val P : ℂ) = 1) :
    ∃ t : ∀ Q, X.RCG i Q → FractionRing (X.O i), ∀ th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i),
      (∀ Q, th i Q lam = t Q) → IsThOf (setTh X th) i ι lam φ s κ 𝔣 χ := by
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hL host_unramFin hD
  have := X.O_complete i
  have key : ∀ Q, ∃ t : X.RCG i Q → FractionRing (X.O i), BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (t δ) = (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) := fun Q => by
    by_cases hQ : BlochKatoReduction.Gen.QOk X i Q
    · obtain ⟨hfin, T, hT⟩ := exists_classTerms hL host_unramFin hD (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1
      obtain ⟨π, hπ, hπl⟩ := exists_isRecMap hA hQ 𝔣
      choose t ht using partialSum_mem hA hG host_unramFin hD (X.resO_ac i) (X.lPrime i).out.ne_zero (X.O_l i) ι hE (X.S0 i)
        (fun P hP => ⟨(algebraMap (X.O i) _ (X.Xv i lam P))⁻¹, by
          rw [map_inv₀, ← IsScalarTower.algebraMap_apply]
          exact (eq_inv_of_mul_eq_one_right (hX P hP)).symm⟩) hT₀ h0 (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hT π hπl
      exact ⟨t, fun _ => ⟨hfin, π, T, hπ, hT, ht⟩⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose t ht using key
  refine ⟨t, fun th e => ⟨(ι T₀)⁻¹, inv_ne_zero ((map_ne_zero ι).2 h0), fun Q hQ => ?_⟩⟩
  obtain ⟨h1, π, T, h2, h3, h4⟩ := ht Q hQ
  exact ⟨h1, π, T, h2, h3, fun δ => (congrArg _ (congrFun (e Q) δ)).trans (h4 δ)⟩

end GlobalTheory.LamTie
