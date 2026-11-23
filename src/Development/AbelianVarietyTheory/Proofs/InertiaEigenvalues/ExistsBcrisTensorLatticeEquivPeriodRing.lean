module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinEquivApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

theorem mem_finiteCocycles_iff_bcrisTensor_coboundary {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (hpow : ∀ v : T.V, ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T)
    (β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B)
    (h1 : ∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B))
    (h2 : ∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b))
    (c : Gl l → T.V) (hc : c ∈ continuousCocycles T.ρ) :
    c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c := by
  have hl : ∀ n : ℕ, (l : ↥LL.1) ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ (b : TW (OB l ↥(OL LL)) T) (g : Gl l) (n : ℕ),
      β ((l : ↥(OL LL)) ^ n • (actB (sQ l) T g b - b)) =
        (l : ↥LL.1) ^ n • (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b) := by
    intro b g n
    have e1 := β.map_smul ((l : ↥(OL LL)) ^ n) (actB (sQ l) T g b - b)
    have e2 : β (actB (sQ l) T g b - b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b :=
      (map_sub β _ _).trans (congrArg (· - β b) (h2 g b))
    have e3 : (((l : ↥(OL LL)) ^ n : ↥(OL LL)) : ↥LL.1) = (l : ↥LL.1) ^ n := by simp
    rw [← e3, ← e2]
    exact e1
  have kx : ∀ (g : Gl l) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : ↥LL.1) ^ n • c g →
      β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (l : ↥LL.1) ^ n • (c g ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) := by
    intro g n x hx
    rw [h1, hx]
    exact (TensorProduct.smul_tmul' _ _ _).symm
  constructor
  · rintro ⟨-, y, hy⟩
    obtain ⟨b, rfl⟩ := β.surjective y
    refine ⟨b, fun g n x hx => β.injective ?_⟩
    exact (kx g n x hx).trans ((congrArg (fun z => (l : ↥LL.1) ^ n • z) (hy g)).trans (key b g n).symm)
  · rintro ⟨b, hb⟩
    refine ⟨hc, β b, fun g => ?_⟩
    obtain ⟨n, hn⟩ := hpow (c g)
    have h3 := (kx g n ⟨_, hn⟩ rfl).symm.trans ((congrArg β (hb g n ⟨_, hn⟩ rfl)).trans (key b g n))
    have h4 := congrArg (fun z => ((l : ↥LL.1) ^ n)⁻¹ • z) h3
    simpa only [inv_smul_smul₀ (hl n)] using h4

theorem exists_equiv : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∃ β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B, (∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧ (∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧ (∀ b, β (TWmap (frobOB l ↥(OL LL)) T b) = φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧ ∀ c ∈ continuousCocycles T.ρ, (c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c) := by
  intro l _ LL T Pl AI hS
  obtain ⟨Ti⟩ := hS
  have hz : ∀ z : ℤ_[l], Ti.eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z :=
    fun z => (Ti.zB z).trans (GlobalTheory.RingIface.aB_zl l z).symm
  exact ⟨linEquiv T Ti.eB hz, linEquiv_one T Ti.eB hz, linEquiv_act T Ti.eB hz Ti.actB,
    linEquiv_frob T Ti.eB hz Ti.frob,
    mem_finiteCocycles_iff_bcrisTensor_coboundary T Pl (exists_pow_smul_mem T) _ (linEquiv_one T Ti.eB hz) (linEquiv_act T Ti.eB hz Ti.actB)⟩

end GlobalTheory.BKGal.CrisTensor
