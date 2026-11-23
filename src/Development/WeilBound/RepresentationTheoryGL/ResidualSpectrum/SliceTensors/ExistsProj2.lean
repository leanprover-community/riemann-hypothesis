module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.MultilinearMemOfSpan
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsNeZeroOfISup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.PLsProj2

theorem proj_fun {Y Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] (act : Γ → Y → Y)
    (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) (T : Submodule ℂ (Y → ℂ))
    (hle : T ≤ ⨆ Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)},
      LinearMap.range Φ.1) (t : Y → ℂ) (ht : t ∈ T) (h0 : t ≠ 0) :
    ∃ p : (Y → ℂ) →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ T, p (fun m => s (act g m)) = ρ g (p s) := by
  have key := PLsAbs2.exists_proj (fun g => LinearMap.funLeft ℂ ℂ (act g)) ρ hρ
    (fun Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)} => Φ.1)
    (fun Φ => Φ.2.2) (hle ht) h0
  obtain ⟨p, hp, he⟩ := key
  exact ⟨p, hp, fun g s hs => he g s (hle hs)⟩

theorem schur {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (φ : τ.V →ₗ[ℂ] τ.V) (hφ : ∀ g x, φ (τ.ρ g x) = τ.ρ g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  obtain ⟨z, hz⟩ := GlobalTheory.LocGL.schur_GL τ.smooth τ.irred ⟨φ, fun g => LinearMap.ext (hφ g)⟩
  exact ⟨z, LinearMap.ext hz⟩

theorem irr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c : ℕ}
    {n : Fin c → ℕ} (τ : ∀ i, SmIrr (GL (Fin (n i)) k)) : (piTensor fun i => (τ i).ρ).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun i => (τ i).irred) fun i => schur (τ i)

end PositivityTheory.Rg.Rs.PLsProj2

namespace PositivityTheory.Rg.Rs

theorem existsProj2 : PositivityTheory.RSHS.LS.ExistsProj := fun E _ _ _ _ n π w τ hτ =>
  PLsProj2.proj_fun (Γ := ∀ i, GL (Fin (n i)) (w.adicCompletion E))
    (fun g (m : ∀ i, GA E (n i)) i => m i * finGL E (n i) (locGL E (n i) w (g i)))
    (piTensor fun i => (τ i).ρ) (PLsProj2.irr τ) (tensorForms π) (PositivityTheory.RSHS.LocalComponentTwist.tensorForms_le_iSup π τ hτ)

end PositivityTheory.Rg.Rs

end
