module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.fixedProjection_apply_equivariant_eq :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (hτ : GroundTheory.Automorphic.IsSmooth τ) (π : UnitaryRep G H) (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) (f : S →ₗ[ℂ] H), Eqv τ π ⊤ f → ∀ x, prj (fixU π U) (f x) = f (fixedProj τ hτ hUc hUo x) := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ π U hUc hUo f hf x
  have hc : (fixU π U).topologicalClosure = fixU π U := (isClosed_fixU π U).submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ (fixU π U).topologicalClosure ↔ v ∈ fixU π U := fun v => by rw [hc]
  have hy : f (fixedProj τ hτ hUc hUo x : S) ∈ fixU π U := fun u hu => by
    rw [← hf.map, (fixedProj τ hτ hUc hUo x).2 u hu]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 hy) fun b hb => ?_
  have hb' : b ∈ fixU π U := (hm _).1 hb
  rw [← map_sub, ← inner_conj_symm, map_eq_zero_iff _ (starRingEnd ℂ).injective]
  let φ : S →ₗ[ℂ] ℂ := (innerSL ℂ b).toLinearMap ∘ₗ f
  have hφ : ∀ k ∈ U, ∀ v, φ (τ k v) = φ v := fun k hk v => by
    show inner ℂ b (f (τ k v)) = inner ℂ b (f v)
    rw [hf.map, ← ContinuousLinearMap.adjoint_inner_left, UnitaryRep.adjoint_map, hb' _ (U.inv_mem hk)]
  exact coinvariantsKer_le_ker_of_invariant hφ (sub_fixedProj_mem hτ hUc hUo x)
