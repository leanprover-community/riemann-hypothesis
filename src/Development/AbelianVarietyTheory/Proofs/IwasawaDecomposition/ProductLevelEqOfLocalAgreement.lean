module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LevCmp

section Glue

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def compHom (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    GAf L n →* GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
  (Matrix.GeneralLinearGroup.map (compAt L v)).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem compHom_eq_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : GAf L n) :
    compHom v x = 1 ↔ (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem compHom_eq_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n) :
    compHom v x = compHom v y ↔
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem mem_of_agree {J J' : Subgroup (GAf L n)} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    {S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (hS : S.Finite) (hJ : NG.IsProdLevel J)
    (hO : NG.HypOutside J χ S) (hO' : NG.HypOutside J' χ' S)
    (hloc : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩)
    (κ : GAf L n) (hκ : κ ∈ J) : ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by

  have hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro u κ hu hκ
    by_cases huS : u ∈ S
    · obtain ⟨h1, h2⟩ := hloc u huS κ hu
      exact ⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩
    · have ht : TrivOutside Sᶜ κ := by
        intro v hv
        apply hu v
        rintro rfl
        exact huS (not_not.mp hv)
      obtain ⟨a1, a2⟩ := hO κ ht
      obtain ⟨b1, b2⟩ := hO' κ ht
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J),
      TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty =>
      intro κ hκ ht
      have ht' : TrivOutside Sᶜ κ := by
        intro v hv
        exact ht v (by simpa using hv)
      obtain ⟨a1, a2⟩ := hO κ ht'
      obtain ⟨b1, b2⟩ := hO' κ ht'
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
    | insert u T huT ih =>
      intro κ hκ ht
      obtain ⟨κu, hκu, hu, hcomp⟩ := hJ κ hκ u
      have hκ1 : κ * κu⁻¹ ∈ J := J.mul_mem hκ (J.inv_mem hκu)
      have ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹) := by
        intro v hv
        rw [← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
        by_cases hvu : v = u
        · subst hvu
          exact ((compHom_eq_iff v κ κu).mpr hcomp.symm)
        · have e1 : compHom v κ = 1 := by
            rw [compHom_eq_one_iff]
            apply ht v
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢
            exact ⟨hv.1, hvu, hv.2⟩
          have e2 : compHom v κu = 1 := by
            rw [compHom_eq_one_iff]
            exact hu v (by simpa using hvu)
          rw [e1, e2]
      obtain ⟨h1', e1⟩ := ih (κ * κu⁻¹) hκ1 ht1
      obtain ⟨h2', e2⟩ := hone u κu hu hκu
      have hprod : κ = κ * κu⁻¹ * κu := by group
      have h' : κ ∈ J' := by
        rw [hprod]; exact J'.mul_mem h1' h2'
      refine ⟨h', ?_⟩
      have s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩ := Subtype.ext hprod
      have s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩ := Subtype.ext hprod
      rw [s1, s2, map_mul, map_mul, e1, e2]
  apply key hS.toFinset κ hκ
  intro v hv
  exfalso
  apply hv
  by_cases h : v ∈ S
  · right; simpa using h
  · left; exact h

theorem levEq_of_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  intro L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc
  have hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩ :=
    fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩
  refine ⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1)
    (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩
  obtain ⟨h'', e⟩ := mem_of_agree hS hJ hO hO' hloc κ h
  exact e

end Glue

end GlobalTheory.LevCmp

end
