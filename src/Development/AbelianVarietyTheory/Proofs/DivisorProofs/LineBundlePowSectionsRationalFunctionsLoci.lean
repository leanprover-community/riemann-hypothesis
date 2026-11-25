module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section

theorem GlobalTheory.HSAmp.pow_sec_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p P e
  have hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e) :=
    GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  rw [mul_one, mul_zero] at hR
  obtain ⟨g, -, hrange, -, hloc⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X) := by
    intro u
    ext x
    obtain ⟨i, hi⟩ := hcov P.L.isLB x
    obtain ⟨j, hj⟩ := hcov P.A.isLB x
    constructor
    · intro h
      exact (hloc u x i j hi hj).2 (h i j hi hj)
    · intro h i' j' hi' hj'
      exact (hloc u x i' j' hi' hj').1 h
  refine ⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩
  · have : g u ∈ Set.range g := ⟨u, rfl⟩
    rw [hrange] at this
    exact this
  · have : f ∈ Set.range g := by rw [hrange]; exact hf
    obtain ⟨u, rfl⟩ := this
    exact ⟨u, key u⟩
