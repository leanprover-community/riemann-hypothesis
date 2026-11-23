module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  first | exact @GlobalTheory.JacMeas.jac_measure | exact GlobalTheory.JacMeas.jac_measure | (intros; apply GlobalTheory.JacMeas.jac_measure <;> assumption)
