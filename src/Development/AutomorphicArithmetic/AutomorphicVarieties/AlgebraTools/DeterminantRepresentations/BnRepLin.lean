module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open Polynomial Matrix UpperTheory.V.W

private noncomputable def UpperTheory.V.AlgebraTools.Det.bnRep_lin {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K) : Representation K G (Fin n → K) where
  toFun g := Matrix.toLin' (ρ g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

private theorem UpperTheory.V.AlgebraTools.Det.bnRep_ss {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra K G) (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem UpperTheory.V.AlgebraTools.Det.bnRep :
    ∀ {n : ℕ} {K G : Type} [Field K] [Group G] (ρ ρ' : G →* Matrix (Fin n) (Fin n) K),
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ' g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ g, (ρ g).charpoly = (ρ' g).charpoly) → ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * ρ' g = ρ g * P := by
  intro n K G _ _ ρ ρ' h h' hc
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt K G (Fin n → K) (Fin n → K)
    (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ') (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ)
    (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ' h') (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ h) (fun g => by
      show (Matrix.toLin' (ρ' g)).charpoly = (Matrix.toLin' (ρ g)).charpoly
      rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact (hc g).symm)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h2, h1⟩, fun g => ?_⟩
  show LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) * ρ' g =
    ρ g * LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact he g
