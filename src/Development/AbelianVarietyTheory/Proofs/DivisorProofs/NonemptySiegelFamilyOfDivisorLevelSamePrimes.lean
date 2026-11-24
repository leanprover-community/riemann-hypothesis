module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReducedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObjectStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
