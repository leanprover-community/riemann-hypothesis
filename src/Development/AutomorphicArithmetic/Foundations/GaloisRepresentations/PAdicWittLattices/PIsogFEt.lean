module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isUnit_nat_of_rat {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}} (s : S ⟶ Sp R) {d : ℕ}
    (hd : 0 < d) : IsUnit (d : Γ(S, ⊤)) := by
  have hR : IsUnit (d : R) := by
    have hq : IsUnit (algebraMap ℚ R (d : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hd.ne')).map _
    simpa using hq
  have h := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h

theorem UpperTheory.Gal.G3.pIsogFEt :
    IsogFEt := by
  intro R _ _ S s A A' _ _ _ _ hA hA' ψ ψ' d hd hψ hψ' h1 h2
  exact GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv S A A' d ψ ψ' hA hA'
    (isUnit_nat_of_rat s hd) ⟨hψ, hψ', h1, h2⟩
