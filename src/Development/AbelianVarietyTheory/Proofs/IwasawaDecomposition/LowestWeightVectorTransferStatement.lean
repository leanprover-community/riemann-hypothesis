module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightVectorTransfer
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowest_weight_vector_transfer : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  first | exact @GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | exact GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | (intros; apply GlobalTheory.JointHarm.OrbitMap.exists_orbit_map <;> assumption)
