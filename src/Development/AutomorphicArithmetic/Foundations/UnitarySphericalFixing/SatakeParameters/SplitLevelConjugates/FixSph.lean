module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeOneOfIsCuspidalMultiProd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.B.fixSph :
    UpperTheory.One.M.B.FixSph := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  let J : Subgroup (GAf L n) :=
    { carrier := {κ | κ ∈ Umax L n ∧ ∀ g, f (g * κ) = f g}
      one_mem' := ⟨one_mem _, fun g => by rw [mul_one]⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun g => by rw [← mul_assoc, hy.2, hx.2]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun g => by
        rw [← hx.2 (g * x⁻¹), inv_mul_cancel_right]⟩ }
  have hAF := hS.1.le hf
  have hlev : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, (1 : J →* ℂˣ) ⟨κ, h⟩ = 1 := by
    obtain ⟨-, N, hN, h⟩ := hAF
    exact ⟨N, hN, fun κ hκ => ⟨⟨hκ.1, h κ hκ⟩, rfl⟩⟩
  have hB : NG.HypOutside J (1 : J →* ℂˣ) {s.v}ᶜ := by
    intro κ hκ
    rw [compl_compl] at hκ
    exact ⟨⟨fun h => h.1, fun h => ⟨h, fun g => congrFun (hfix κ h hκ) g⟩⟩, fun _ => rfl⟩
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ h => h⟩ : S ≤ _) hf
  have hT : f ∈ NG.TypeSp a.ρ J (1 : J →* ℂˣ) := ⟨hAF, fun κ => by
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact funext κ.2.2⟩
  have h := GlobalTheory.SphHyp.isSpherical_of_hypOutside L n a S hS J 1 hlev _ hB f hiso hT hf0 s (by simp) σ hσ
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ).symm h
