module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  first | exact @GlobalTheory.HatNF.vec_bigPt_eq_radial | exact GlobalTheory.HatNF.vec_bigPt_eq_radial | (intros; apply GlobalTheory.HatNF.vec_bigPt_eq_radial <;> assumption)
