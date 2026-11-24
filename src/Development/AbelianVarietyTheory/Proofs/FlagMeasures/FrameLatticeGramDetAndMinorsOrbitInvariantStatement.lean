module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariant
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  first | exact @GlobalTheory.FrameGram.main | exact GlobalTheory.FrameGram.main | (intros; apply GlobalTheory.FrameGram.main <;> assumption)
