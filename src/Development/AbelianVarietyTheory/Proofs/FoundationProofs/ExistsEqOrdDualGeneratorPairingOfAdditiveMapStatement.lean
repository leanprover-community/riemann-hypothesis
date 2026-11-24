module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)), ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  first | exact @GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | exact GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | (intros; apply GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | exact GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | (intros; apply GlobalTheory.Ord2.SelPerp.coef_free_pairSurj <;> assumption)
