module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumDen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory
namespace FactorAway

theorem factor_away : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra.FinitePresentation R A] (p : Ideal B) [p.IsPrime]
    (φ : A →ₐ[R] Localization.AtPrime p), ∃ (g : B) (hg : g ∉ p)
      (ψ : A →ₐ[R] Localization.Away g), ∀ a, Localization.awayLift
        (algebraMap B (Localization.AtPrime p)) g
        (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) (ψ a) = φ a := by
  intro R A B _ _ _ _ _ _ p _ φ
  let φ' : B ⊗[R] A →ₐ[B] Localization.AtPrime p :=
    Algebra.TensorProduct.lift (Algebra.ofId B _) φ (fun _ _ => Commute.all _ _)
  obtain ⟨g, hg, s, ι, hι⟩ := SpreadOut.spread_out B (B ⊗[R] A) p φ'
  refine ⟨g, hg, (s.restrictScalars R).comp Algebra.TensorProduct.includeRight, fun a => ?_⟩
  have hext : (Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
      (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl))) =
      (ι : Localization.Away g →+* Localization.AtPrime p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext b
    simp [Localization.awayLift]
  have h1 := congrArg (fun h => h ((1 : B) ⊗ₜ[R] a)) hι
  simp only [AlgHom.comp_apply, φ', Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h1
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply]
  rw [hext]
  exact h1

end FactorAway
end GlobalTheory
