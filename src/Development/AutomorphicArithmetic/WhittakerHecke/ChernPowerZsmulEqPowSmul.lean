module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem cohomology_cast_zsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (c : ℤ)
    (x : Ht q E n i) : Ht.cast hn hi (c • x) = c • Ht.cast hn hi x := by
  subst hn hi
  rfl

theorem UpperTheory.chernPower_zsmul_eq_pow_smul :
    ∀ (q : ℕ) {E : Spc} (y : Ht q E 2 1) (m : ℤ) (j : ℕ), cpow q (m • y) j = (m ^ j) • cpow q y j := by
  intro q E y m j
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pow_zero, one_smul]
  | succ k ih =>
    rw [cpow_succ, cpow_succ, ih, map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul,
      ← pow_succ', cohomology_cast_zsmul]
