module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumExLoc_of :
    SecFun → FunSec → FibFin → SumExLoc := by
  intro hSF hFS hFF q _ i Z S p _ w hw A hζ a
  obtain ⟨ζ⟩ := hζ
  haveI : IsFinite A.r := Sq.finite A
  have hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ) :=
    ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm
  obtain ⟨φ, hφ, hv⟩ := hSF q i A.V (ζ.map A.r.appTop.hom) a
  obtain ⟨ψ, hψ, hs⟩ := hw A φ hφ
  obtain ⟨b, hb⟩ := hFS q i A.U ζ ψ hψ
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hfin : (fib A.r x).Finite := hFF A.r Ω x
  have hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ) := by
    intro z hz
    have hz' : z ≫ A.r = x := hz
    rw [hv Ω z, hgen, res_res, hz']
  rw [hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hzm => ?_
  rw [hz z (hfin.mem_toFinset.mp hzm), mul_smul]
