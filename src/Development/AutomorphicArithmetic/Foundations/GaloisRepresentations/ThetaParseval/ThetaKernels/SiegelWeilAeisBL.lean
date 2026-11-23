module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisHalf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisMult
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Aeis
def EisBLW_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
theorem eisBLW_k : _root_.PositivityTheory.SiegelWeilFormula.Aeis.EisBLW_k := by
  intro F E _ _ _ _ _ σ B n Y hB hn χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨t₀, v, hv, hvh⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisHalf_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨A, H, t₁, hA, hAne, hHh, hHs⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.siegelMult_w_k hB hn χ hχ c hc hb hK ha s₁ f hf
  have hHv : ∀ s' : ℂ, max t₀ t₁ < s'.re → ∀ x, (H s').1 x = A s' * (v s').1 x := by
    intro s' hs' x
    have h1 := hHs s' (lt_of_le_of_lt (le_max_right _ _) hs') x
    have h2 := (hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x).mul_left (A s')
    exact h1.unique h2
  let Ehat : ℂ → G2 σ Y → ℂ := fun s' x => if max t₀ t₁ < s'.re then (v s').1 x else (H s').1 x / A s'
  refine ⟨Ehat, ⟨max t₀ t₁, ?_, ?_⟩, ?_⟩
  · intro s' hs' x
    simp only [Ehat, if_pos hs']
    exact hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x
  · intro x
    have hd : DifferentiableOn ℂ (fun s' => evAt x (v s')) {s' : ℂ | t₀ < s'.re} :=
      hvh (evAt x) (isGrowForm_evAt x)
    have hd' : DifferentiableOn ℂ (fun s' => (v s').1 x) {s' : ℂ | max t₀ t₁ < s'.re} :=
      (hd.mono fun s' (hs' : max t₀ t₁ < s'.re) => (show t₀ < s'.re from lt_of_le_of_lt (le_max_left _ _) hs'))
    refine hd'.congr fun s' hs' => ?_
    simp only [Ehat, if_pos (show max t₀ t₁ < s'.re from hs')]
  · intro s₀
    obtain ⟨k, U, u, hUo, hs₀U, hud, hUA⟩ := GlobalTheory.CompanionTheory.Entire.local_factorisation A hA hAne s₀
    refine ⟨k, U, fun s' => (u s')⁻¹ • H s', hUo.mem_nhds hs₀U, ?_, ?_⟩
    · intro s' hs' hne x
      obtain ⟨hu, hAs⟩ := hUA s' hs'
      have hpow : (s' - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      show (u s')⁻¹ * (H s').1 x = (s' - s₀) ^ k * Ehat s' x
      by_cases hre : max t₀ t₁ < s'.re
      · simp only [Ehat, if_pos hre]
        rw [hHv s' hre x, hAs]
        field_simp
      · simp only [Ehat, if_neg hre]
        rw [hAs]
        field_simp
    · intro μ hμ
      have h1 : DifferentiableOn ℂ (fun s' => (u s')⁻¹) U := hud.inv fun s' hs' => (hUA s' hs').1
      have h2 : DifferentiableOn ℂ (fun s' => μ (H s')) U := (hHh μ hμ).differentiableOn
      refine (h1.mul h2).congr fun s' _ => ?_
      simp [map_smul, smul_eq_mul]
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
