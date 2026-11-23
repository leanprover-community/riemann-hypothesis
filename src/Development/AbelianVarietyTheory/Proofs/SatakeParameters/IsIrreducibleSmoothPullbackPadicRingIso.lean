module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
