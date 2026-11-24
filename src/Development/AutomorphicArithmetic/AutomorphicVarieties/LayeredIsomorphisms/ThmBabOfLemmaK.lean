module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.GaloisCohomology

namespace UpperTheory.V.Win

theorem thmBab_of_lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hFW : Published.FerreroWashington) (hK : ∃ CK : ℝ, LemmaK CK) : ∃ K : BConst, ∀ Ct : ℝ, 1 ≤ Ct → ThmBab K Ct :=
  have hA : Two.TowerBound := fun l _ L _ _ R h => PropA.aBound_of_isTower hP hF hT l L R h
  thmBab_of hK (Two.fixedIn hFW hA) (Two.twoIn hFW hA)

end UpperTheory.V.Win
