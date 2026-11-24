module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchASpan

theorem mem_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  intro F _ _ κ _ Φ hΦ
  refine (Submodule.span_le.2 ?_) hΦ
  rintro _ ⟨f, g, hg, rfl⟩
  let L : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f g
      map_add' := fun a b => by funext x; simp only [pureA, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have h : L g ∈ Submodule.map L (Submodule.span ℂ _) :=
    Submodule.mem_map_of_mem (GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg)
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, ⟨φ, hφ1, hφ2, rfl⟩, rfl⟩
  exact ⟨f, φ, ⟨hφ1, hφ2⟩, rfl⟩

end GlobalTheory.SchASpan

end
