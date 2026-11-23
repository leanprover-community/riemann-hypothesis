module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedMatrixGroupImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LinRedLie

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  one_mem' := hG.one_mem
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  inv_mem' := fun {u} hu => by
    have h := hG.inv_mem _ hu
    rw [← Matrix.coe_units_inv] at h
    exact h

theorem isClosed_unitsOf (hG : GlobalTheory.LinRed.IsLinRed G) :
    IsClosed (unitsOf hG : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  refine isClosed_of_closure_subset fun u hu => ?_
  refine hG.closed _ u.isUnit ?_
  exact closure_mono (fun v hv => hv) (map_mem_closure Units.continuous_val hu (fun v hv => hv))


open scoped Matrix.Norms.L2Operator in
theorem exists_subspace (hG : GlobalTheory.LinRed.IsLinRed G) :
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ 𝔤, NormedSpace.exp X ∈ G) ∧
      ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
        ∀ X ∈ U, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  obtain ⟨𝔤, h⟩ := GlobalTheory.CompanionTheory.ClosedSubgroupUnits.exists_isExpLieAlgebra (unitsOf hG) (isClosed_unitsOf hG)
  obtain ⟨U, hUo, h0, -, hU⟩ := h.exists_nhds
  exact ⟨𝔤, fun X hX => h.expUnit_mem X hX, U, hUo, h0, fun X hXU hX => hU X hXU hX⟩

theorem exists_lieAlgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧
      ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  intro n G hG
  obtain ⟨𝔤, hexp, U, hUo, h0, hU⟩ := exists_subspace hG
  refine ⟨𝔤, fun X => ⟨fun hX t => hexp _ (𝔤.smul_mem t hX), fun hX => ?_⟩,
    U, hUo.mem_nhds h0, hU⟩
  have hc : Continuous fun t : ℝ => t • X := continuous_id.smul continuous_const
  have hev : ∀ᶠ t : ℝ in 𝓝 0, t • X ∈ U :=
    hc.continuousAt.eventually_mem (by simpa using hUo.mem_nhds h0)
  obtain ⟨t, htU, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, t • X ∈ U ∧ t ∈ ({0}ᶜ : Set ℝ)).exists
  exact (𝔤.smul_mem_iff ht).1 (hU _ htU (hX t))

end GlobalTheory.CompanionTheory.LinRedLie
