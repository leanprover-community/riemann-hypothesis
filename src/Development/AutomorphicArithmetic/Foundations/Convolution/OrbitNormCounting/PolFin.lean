module

public import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem UpperTheory.ConvolutionTheory.G3.polFin :
    UpperTheory.ConvolutionTheory.G3.PolFin := by
  intro E _ _ _ hU n S hS C hC hC1
  choose γ hγ0 hγ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E n w (C w) (hC w)
  let g : Pl E → WithZero (Multiplicative ℤ) := fun w => if C w ⊆ GlobalTheory.LFun.KGL w (n := n) then 1 else γ w
  have hlev : ∀ w : Pl E, IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) := fun w =>
    ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩
  refine (GlobalTheory.BCT.GeoFin.finite_ell_bounded E n S hS g
    (fun w => by by_cases h : C w ⊆ GlobalTheory.LFun.KGL w (n := n) <;> simp [g, h, hγ0])
    (hC1.mono fun w h => by simp [g, h])).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP, fun w hw => ?_⟩
  obtain ⟨y, hy, e⟩ := hPS w hw
  rw [← e]
  by_cases h : C w ⊆ GlobalTheory.LFun.KGL w (n := n)
  · simp only [g, if_pos h, inv_one]
    exact GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E n w (hlev w) y (h hy)
  · simp only [g, if_neg h]
    exact hγ w y hy
