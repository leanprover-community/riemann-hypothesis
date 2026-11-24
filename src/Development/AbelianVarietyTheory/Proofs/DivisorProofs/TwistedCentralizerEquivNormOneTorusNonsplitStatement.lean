module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEquivNormOneTorusNonsplit
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  first | exact @GlobalTheory.TwLat.twCent_equiv_torus | exact GlobalTheory.TwLat.twCent_equiv_torus | (intros; apply GlobalTheory.TwLat.twCent_equiv_torus <;> assumption)
