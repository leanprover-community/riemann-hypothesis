module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem _root_.GlobalTheory.T.equivalence_generated_torus_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 := by
  first | exact @GlobalTheory.UCls.torus_eqvGen_main | exact GlobalTheory.UCls.torus_eqvGen_main | (intros; apply GlobalTheory.UCls.torus_eqvGen_main <;> assumption)
