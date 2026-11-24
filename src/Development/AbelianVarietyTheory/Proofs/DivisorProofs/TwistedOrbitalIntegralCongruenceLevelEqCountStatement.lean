module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCount
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Q.Separable → Fits w e B Q u → u = 1 + algebraMap K.O B.A t * B.g → ∀ (γ : GLw n w) (hγ : γ ∈ UL n w), IsModel w e B u x γ → twOrb (MonoidHom.id (UL n w)) (KL n w) ⟨γ, hγ⟩ (({g : UL n w | g.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapOrb.twOrb_congruence_eq_N | exact GlobalTheory.KapOrb.twOrb_congruence_eq_N | (intros; apply GlobalTheory.KapOrb.twOrb_congruence_eq_N <;> assumption)
