module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct <;> assumption)
