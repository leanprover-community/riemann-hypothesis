module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitary
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
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

theorem _root_.GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) R), IsUnit J.det → ∀ (A : Matrix (Fin M) (Fin 2) R) (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R), B * A = 1 → Formalism.UG.cT c A * J = H * B → J * A = Formalism.UG.cT c B * H → ∀ G : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c G * J * G = J → G * (1 - A * B) = 1 - A * B → G = emb A B (B * G * A) ∧ Formalism.UG.cT c (B * G * A) * H * (B * G * A) = H := by
  first | exact @GlobalTheory.PlaneSU.eq_emb_of_fix | exact GlobalTheory.PlaneSU.eq_emb_of_fix | (intros; apply GlobalTheory.PlaneSU.eq_emb_of_fix <;> assumption)
