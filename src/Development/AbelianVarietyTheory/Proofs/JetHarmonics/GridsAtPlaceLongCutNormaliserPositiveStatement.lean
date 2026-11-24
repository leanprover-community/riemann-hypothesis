module

public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositive
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.grids_at_place_longCut_normaliserPositive : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  first | exact @GlobalTheory.GridAtPlace.main | exact GlobalTheory.GridAtPlace.main | (intros; apply GlobalTheory.GridAtPlace.main <;> assumption)
