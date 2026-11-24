module

public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualMatrixFrameFvec
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
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.exists_dual_matrix_frame_fvec : ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)), inWb k r z' → 0 < Tz k r z' → ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧ (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧ ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  first | exact @GlobalTheory.HatNF.DualFrame.exists_dual_matrix | exact GlobalTheory.HatNF.DualFrame.exists_dual_matrix | (intros; apply GlobalTheory.HatNF.DualFrame.exists_dual_matrix <;> assumption)
