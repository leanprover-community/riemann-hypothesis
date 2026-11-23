module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.WhittakerRelevance

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.trace_restrict_eq_of_hasFinTrace :
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (Q Q' : Submodule ℂ S) [FiniteDimensional ℂ Q'] (g : S →ₗ[ℂ] S) (t : ℂ) (m : Module.End ℂ Q') (e : Q' →ₗ[ℂ] S), Q ≤ Q' → HasFinTrace g t → (∀ x, g x ∈ Q) → (∀ x : Q', ((m x : Q') : S) = g (e x)) → (∀ x : Q', (x : S) ∈ Q → e x = x) → LinearMap.trace ℂ Q' m = t := by
  intro S _ _ Q Q' _ g t m e hQ hg hgQ hm he
  obtain ⟨hfd, hr⟩ := hg
  haveI := hfd
  have hWQ : LinearMap.range g ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hgQ x
  let p : Q' →ₗ[ℂ] LinearMap.range g :=
    (g ∘ₗ e).codRestrict (LinearMap.range g) fun x => LinearMap.mem_range_self g (e x)
  let q : LinearMap.range g →ₗ[ℂ] Q' := Submodule.inclusion (hWQ.trans hQ)
  have e1 : m = q ∘ₗ p := by
    ext x
    exact hm x
  have e2 : g.restrict (p := LinearMap.range g) (q := LinearMap.range g)
      (fun v _ => LinearMap.mem_range_self g v) = p ∘ₗ q := by
    ext x
    exact congrArg g (he (q x) (hWQ x.2)).symm
  rw [e1, LinearMap.trace_comp_comm', ← e2, hr]
