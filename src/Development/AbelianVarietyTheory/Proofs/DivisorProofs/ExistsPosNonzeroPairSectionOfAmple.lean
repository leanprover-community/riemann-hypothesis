module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem exists_pos_nonzero_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ),
      ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  intro k _ X _ p D hX P hA a
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a 0
  obtain ⟨b, hb, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M P.A hA {genericPoint X}
    (Set.finite_singleton _)
  have hA1 := (Pair.rep_base k X p P).2.1
  have hAb := Pair.rep_pow k X p P 0 1 P.A b hA1
  have hN := Pair.rep_tens k X p P a 0 _ _ M (P.A.pow b) hM hAb
  have e1 : a + (b : ℤ) * 0 = a := by ring
  have e2 : (0 : ℤ) + (b : ℤ) * 1 = b := by ring
  rw [e1, e2] at hN
  obtain ⟨e, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P a b _ hN
  have hmem : e u ∈ P.H a b := by
    have : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨b, e u, hb, fun h0 => ?_, hmem⟩
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  rw [h0] at hU
  have z : P.loc a b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  exact hz _ hU

end GlobalTheory.HSNef
