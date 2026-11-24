module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
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

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfCharGL_tw {N : ℕ} {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (z : ℂ) : HasInfCharGL (tw V z) τ (m.map (· + z)) := by
  have hW := GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi h (GlobalTheory.CuspRep.Model.absC E z)
  rw [GlobalTheory.CuspRep.Model.expo_absC] at hW
  exact hW

theorem prod_cancel (m₁ m₂ : Multiset ℂ) (u : ℂ) (r s : ℕ) :
    ((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod = ((m₁ + m₂).map (u + ·)).prod := by
  rw [Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem hasInfCharGL_node {r s : ℕ} {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {τ : E →+* ℂ}
    {m₁ m₂ : Multiset ℂ} (h₁ : HasInfCharGL U₁ τ m₁) (h₂ : HasInfCharGL U₂ τ m₂) :
    HasInfCharGL (Submodule.span ℂ {φ | MemInd2 (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) φ ∧
      φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) τ (m₁ + m₂) := by
  refine ⟨by rw [Multiset.card_add, h₁.1, h₂.1], fun u φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem F hF =>
    have hc : cap τ u F = (((m₁.map (· + (s : ℂ) / 2)).map (u - (s : ℂ) / 2 + ·)).prod *
        ((m₂.map (· + -(r : ℂ) / 2)).map (u + (r : ℂ) / 2 + ·)).prod) • F :=
      PositivityTheory.Rg.Rs.PInfInd2A.casimir_on_parabolic_induction (n := ![r, s]) (tw U₁ ((s : ℂ) / 2)) (tw U₂ (-(r : ℂ) / 2)) τ _ _
        (hasInfCharGL_tw h₁ _) (hasInfCharGL_tw h₂ _) u F hF.1
    rw [hc, prod_cancel]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem hasInfCharGL_space {N : ℕ} (t : Tr E N) (τ : E →+* ℂ) (m : Multiset ℂ) (h : t.InfOf τ m) :
    HasInfCharGL t.space τ m := by
  induction t generalizing m with
  | leaf V z =>
    obtain ⟨m₀, h₀, rfl⟩ := h
    exact hasInfCharGL_tw h₀ z
  | node t₁ t₂ ih₁ ih₂ =>
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := h
    exact hasInfCharGL_node (ih₁ m₁ h₁) (ih₂ m₂ h₂)

theorem infTree : InfTree := fun _ _ _ _ _ t τ m h => hasInfCharGL_space t τ m h

end PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

end
