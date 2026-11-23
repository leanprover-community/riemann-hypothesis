module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystemStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentralStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentatStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsWeightIdempotentStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open GlobalTheory.BI
namespace GlobalTheory.BI

def weightStabiliser {L G : Type} [Field L] [Group G] (B : Subgroup G) (hB : B.Normal)
    (lam : B →* Lˣ) : Subgroup G where
  carrier := {g | ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b}
  one_mem' := by
    intro b b' h
    have : b' = b := Subtype.ext (by simpa using h)
    rw [this]
  mul_mem' := by
    intro g h hg hh b b' e
    have hc : g⁻¹ * (b : G) * g ∈ B := by
      simpa using hB.conj_mem b b.2 g⁻¹
    have h1 := hg b ⟨_, hc⟩ rfl
    have h2 := hh ⟨_, hc⟩ b' (by rw [e]; simp [mul_assoc])
    rw [h2, h1]
  inv_mem' := by
    intro g hg b b' e
    exact (hg b' b (by rw [e]; simp [mul_assoc])).symm

theorem nontrivial_of_isIrreducible {L G V : Type} [Field L] [Group G] [AddCommGroup V]
    [Module L V] (ρ : Representation L G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem irrChar_linear_or_induced : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  intro L _ _ _ G _ _ χ hG ⟨n, ρ, hρ, hχ⟩
  have hχ' : ∀ g, χ g = ρ.character g := fun g => by simpa using hχ g
  haveI := nontrivial_of_isIrreducible ρ hρ
  by_cases hR : ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ
  · exact Or.inr hR
  left
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible L G (Fin n → L) ρ hρ
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    refine GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central G (Module.End L (Fin n → L)) ρ hG ?_
    intro B hB hBc
    obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L B (Fin n → L) (ρ.comp B.subtype)
      (fun a b => hBc a a.2 b b.2)
    obtain ⟨e, he0, hee, heB, heT, heN⟩ := GlobalTheory.T.exists_weight_idempotent_of_eigenvector L G (Fin n → L) ρ B
      (weightStabiliser B hB lam) lam v hB hv hlam (fun _ => Iff.rfl)
    obtain ⟨ψ, hψ, hind⟩ := GlobalTheory.T.character_eq_induced_of_imprimitivity_system L G (Fin n → L) ρ _ e hρ he0 hee heT heN
    have hT : weightStabiliser B hB lam = ⊤ := by
      by_contra hT
      exact hR ⟨_, hT, ψ, hψ, funext fun g => (hχ' g).trans (hind g)⟩
    have he1 : e = 1 := hs1 e he0 hee (fun g => heT g (hT ▸ Subgroup.mem_top g))
    intro b hb g
    have := heB ⟨b, hb⟩
    rw [he1, mul_one] at this
    change ρ b = _ at this
    rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  obtain ⟨lam, v, hv, hlam⟩ := GlobalTheory.T.exists_character_eigenvector_of_commuting_representation L G (Fin n → L) ρ hcomm
  exact ⟨lam, fun g => (hχ' g).trans (hs2 lam v hv hlam g)⟩

end GlobalTheory.BI
