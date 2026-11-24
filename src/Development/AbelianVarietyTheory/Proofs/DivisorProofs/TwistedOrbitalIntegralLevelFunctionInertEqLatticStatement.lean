module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLattic
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

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | exact GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum | (intros; apply GlobalTheory.TwOrbLevel.twOrb_level_eq_stSum <;> assumption)
