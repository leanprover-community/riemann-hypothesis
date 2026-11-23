module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : _root_.GlobalTheory.CuspRep.IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
