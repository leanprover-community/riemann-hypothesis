module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfCommutingEndAlgHom
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_multilinearMap_of_commuting_endAlgHom : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V), (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) → ∃ F : (∀ v, Wv v) →ₘₗ[ℂ] V, F w = y ∧ ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u), Φ v A (F x) = F (Function.update x v (A (x v))) := by
  exact @GlobalTheory.exists_multilinear_of_commuting_endAlgHom
