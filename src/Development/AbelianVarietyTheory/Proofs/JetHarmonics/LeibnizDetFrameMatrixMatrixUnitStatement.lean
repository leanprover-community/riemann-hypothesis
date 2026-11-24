module

public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.leibniz_det_frameMatrix_matrixUnit : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  first | exact @GlobalTheory.HatNF.DetLeibniz.det_leibniz | exact GlobalTheory.HatNF.DetLeibniz.det_leibniz | (intros; apply GlobalTheory.HatNF.DetLeibniz.det_leibniz <;> assumption)
