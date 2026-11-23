module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommonRepresentativesPeriodLatticeHalves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepComb
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

theorem _root_.GlobalTheory.T.common_representatives_period_lattice_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  first | exact @GlobalTheory.CommonReps.common_reps_halves | exact GlobalTheory.CommonReps.common_reps_halves | (intros; apply GlobalTheory.CommonReps.common_reps_halves <;> assumption)
