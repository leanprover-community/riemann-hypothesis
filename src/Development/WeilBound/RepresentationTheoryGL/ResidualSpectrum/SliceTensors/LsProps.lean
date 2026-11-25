module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.LS

def RestrictAtPoint : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N c : ℕ) (n : Fin c → ℕ)
  (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (X : Type) [AddCommGroup X]
  [Module ℂ X] (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X)
  (F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w ρ), F.1 ≠ 0 →
    ∃ L : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ), (∀ v, L v ∈ tensorForms π) ∧ L ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : X),
        L (ρ p v) = fun m => L v fun i => m i * finGL E (n i)
          (locGL E (n i) w (leviProj (w.adicCompletion E) (stdBlocks n h) p i))

def ExistsProj : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (c : ℕ) (n : Fin c → ℕ)
  (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))),
  (∀ i, (π i).IsLocComp w (τ i)) → ∀ t ∈ tensorForms π, t ≠ 0 →
    ∃ p : ((∀ i, GA E (n i)) → ℂ) →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, p t ≠ 0 ∧
      ∀ (g : ∀ i, GL (Fin (n i)) (w.adicCompletion E)), ∀ s ∈ tensorForms π,
        p (fun m => s fun i => m i * finGL E (n i) (locGL E (n i) w (g i))) = piTensor (fun i => (τ i).ρ) g (p s)

def FrobRecip : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (σ' : SmIrr (GL (Fin N) k)) (W : Type) [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W) (ℓ : σ'.V →ₗ[ℂ] W), ℓ ≠ 0 →
    (∀ (p : parab k (stdBlocks n h)) (v : σ'.V), ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) →
      ∃ f : σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)),
        f.toLinearMap ≠ 0

end PositivityTheory.RSHS.LS

end
