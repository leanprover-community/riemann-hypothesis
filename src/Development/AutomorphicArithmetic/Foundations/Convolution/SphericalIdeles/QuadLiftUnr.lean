module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelfStatement
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftUnr
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftUnr :
    UpperTheory.ConvolutionTheory.Sph.QuadLiftUnr := by
  intro K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hram, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  exact UpperTheory.ConvolutionTheory.Sph.liftUnr K M hp a ha π fun η hη =>
    GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha _ η (w.under (𝓞 K)) B hB ((UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram).2.2 η hη)
