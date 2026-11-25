module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}


variable (θ V) in
abbrev Mc : Submodule ℂ (GA D V → ℂ) := GlobalTheory.Cusp.cuspForms θ V ⊥

theorem mem_Mc_iff {φ : GA D V → ℂ} : φ ∈ Mc θ V ↔ IsAutFunSm θ V φ ∧ IsCuspFun V φ := by
  refine ⟨fun h => (mem_cuspForms.1 h).1, fun h => mem_cuspForms.2 ⟨h, ?_⟩⟩
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨Submodule.span ℂ {φ}, inferInstance, fun k hk => ?_⟩
  rw [Subgroup.mem_bot.1 hk]
  exact Submodule.subset_span (by simp)

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) where
  toFun φ := ⟨Rder θ V τ X φ.1, mem_Mc_iff.2
    ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX (mem_Mc_iff.1 φ.2).1,
      GlobalTheory.CuspLie.isCuspFun_Rder hθ hX (mem_Mc_iff.1 φ.2).1 (mem_Mc_iff.1 φ.2).2⟩⟩
  map_add' f g := Subtype.ext (Rder_add (mem_Mc_iff.1 f.2).1.smooth (mem_Mc_iff.1 g.2).1.smooth hX)
  map_smul' c f := Subtype.ext (Rder_smul c f.1 τ X)

def io (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) : Mc θ V →ₗ[ℂ] L2cusp V μ :=
  GlobalTheory.Cusp.cuspToL2 ⊥ μ
    (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ

theorem io_injective (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) :
    Function.Injective (io (V := V) μ hθ) := cusp_form_toL2_injective _ hθ

def derInf (hθ : IsInfFam θ) (X : GlobalTheory.SmoothForms.LieN V) : Module.End ℂ (Mc θ V) :=
  ∑ τ, der hθ τ (X := (X τ).1) (X τ).2

def IsKLie {n : ℕ} (e : Fin n → Bool) (y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  yᴴ = -y ∧ y * Formalism.REAL.Jm e = Formalism.REAL.Jm e * y

end GlobalTheory.CompanionTheory.HCCusp
