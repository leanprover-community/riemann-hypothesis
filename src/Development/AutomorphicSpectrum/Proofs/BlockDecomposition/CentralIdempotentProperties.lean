module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.Ty.Fin CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem nonempty_iso_iff_equiv (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ Nonempty (Representation.Equiv τ.ρ σ.ρ) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩

theorem zIdem_act (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by
  have h := centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)
  rw [zIdem_eq_centralIdem, h]
  by_cases hc : Nonempty (τ ≅ σ)
  · rw [if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]

theorem eq_of_act (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])

theorem zIdemFacts : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ hτ
    refine ⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩
    · rw [map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
    · rw [map_mul, map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
  · intro Γ _ _ τ σ hτ hσ hne
    refine eq_of_act _ _ fun W hW => ?_
    rw [map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]
    by_cases h1 : Nonempty (τ ≅ W)
    · by_cases h2 : Nonempty (σ ≅ W)
      · exact absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne
      · simp [h2]
    · simp [h1]
  · intro Γ _ _ τ σ hτ hσ hiso
    rw [zIdem_act τ σ hτ hσ, if_pos hiso]
  · intro Γ _ _ I _ V hV hinj hex
    classical
    refine eq_of_act _ _ fun W hW => ?_
    obtain ⟨i₀, ⟨e⟩⟩ := hex W hW
    have hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) =
        if i = i₀ then (1 : Module.End ℂ W) else 0 := by
      intro i
      rw [zIdem_act (V i) W (hV i) hW]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos ⟨e.symm⟩, if_pos rfl]
      · rw [if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]

    rw [map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]
    simp

end GlobalTheory.CompanionTheory.TyFin
