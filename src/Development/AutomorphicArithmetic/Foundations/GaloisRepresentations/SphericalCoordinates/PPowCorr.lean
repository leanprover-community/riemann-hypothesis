module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powCorr_of :
    UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PowCorr := by
  intro hPw hPt p _ D G L gb N N' h X X' c₁ c₂ ρ D' S hact ga hcomp k α
  have w₁ := hPw p D G L gb N N' 1 X X' c₁ k
  have w₂ := hPw p D G L gb N N' h X X' c₂ k
  refine ⟨?_, ?_⟩
  · intro P P'' hP hP'' hga z
    obtain ⟨hu, hex⟩ := hcomp P P'' hP hP'' hga
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    have f'' := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P'' hP''
    apply KS.PowPB.pow_left_hom_ext
    · simp only [Category.assoc, (w₂.2.2.2 α).1, w₁.1]
      simp only [← Category.assoc, f.1, f''.1]
      exact hu
    · intro i
      simp only [Category.assoc, (w₂.2.2.2 α).2 i, w₁.2.1 i]
      simp only [← Category.assoc, f.2.1, f''.2.1]
      rw [hex, Category.assoc, ← w₁.2.2.1, ← Category.assoc, ← hact P'' hP'']
      rfl
  · intro P hP hinj z z' heq
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    refine (f.2.2.2.1 z z').2 (fun j => hinj (z j) (z' j) ?_)
    have e := congrArg (· ≫ Over.Hom.left (KS.pr X.univ.A j)) heq
    simp only [Category.assoc, w₁.2.1 j] at e
    simpa only [← Category.assoc, f.2.1] using e
