module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
