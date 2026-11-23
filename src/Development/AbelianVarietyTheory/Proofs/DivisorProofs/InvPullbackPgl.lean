module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem pull_htCast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast, (hA q).1, ih]

theorem inv_pullback_pgl (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) :
    Inv q (pullback V (PGL.pr N)) := fun U ⟨x⟩ => hE U ⟨Sx.map (pullback.fst V (PGL.pr N)) x⟩

end GlobalTheory.EtC
