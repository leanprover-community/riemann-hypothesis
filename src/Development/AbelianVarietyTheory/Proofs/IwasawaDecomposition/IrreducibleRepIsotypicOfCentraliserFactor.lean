module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.CuspRep.CompUniq

theorem isotypic : ∀ (G H V W W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (s : H →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'), ρ.IsIrreducible → σ.IsIrreducible → σ'.IsIrreducible → (∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y)) → ∀ f : σ.IntertwiningMap (ρ.comp s), f ≠ 0 → (⨆ f : σ.IntertwiningMap (ρ.comp s), LinearMap.range f.toLinearMap) = ⊤ ∧ ∀ f' : σ'.IntertwiningMap (ρ.comp s), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
  intro G H V W W' _ _ _ _ _ _ _ _ ρ s σ σ' hρ hσ hσ' hc f hf
  have hP : GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) = ⊤ := by
    rcases ((isIrreducible_iff ρ).1 hρ).2 (GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s)) (fun g v hv => by
      obtain ⟨u, hu⟩ := hc g
      have h1 := GlobalTheory.CuspRep.LocUniq.isoPart_comm σ (ρ.comp s) (ρ ((s u)⁻¹ * g)) (fun y x => by
        simp only [MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, (hu y).eq]) hv
      have h2 := GlobalTheory.CuspRep.LocUniq.isoPart_act σ (ρ.comp s) u h1
      rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h2) with h | h
    · refine absurd ?_ hf
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine LinearMap.ext fun v => ?_
      have h3 : f.toLinearMap v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (ρ.comp s) :=
        Submodule.mem_iSup_of_mem f ⟨v, rfl⟩
      rw [h] at h3
      rw [(Submodule.mem_bot ℂ).1 h3]
      rfl
    · exact h
  refine ⟨hP, fun f' hf' => ?_⟩
  haveI := hσ
  haveI := hσ'
  exact GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ σ' (ρ.comp s) hP f' hf'

end GlobalTheory.CuspRep.CompUniq
