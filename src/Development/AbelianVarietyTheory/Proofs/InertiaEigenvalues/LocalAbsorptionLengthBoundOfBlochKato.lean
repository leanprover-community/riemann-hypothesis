module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatumStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.DimensionInputTwoOfBlochKato
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
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

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ClosingStatement

theorem main : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  intro hBK hTD hEC D _ _ _
  have h5 : Formalism.MainNotions.LocalSituation.Conclusion5 D := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D
  have a1 : BlochKatoDuality.adm1 D := dimension_input_one_of_bloch_kato D h5
  have a2 : BlochKatoDuality.adm2 D := dimension_input_two_of_bloch_kato D h5
  have a3 : BlochKatoDuality.adm3 D := fun l _ K => GlobalTheory.T.tate_H2_period_datum hTD l (D.loc l) K
  have a5 : BlochKatoDuality.adm5 D := fun l _ K => GlobalTheory.T.finite_H1_period_datum hTD l (D.loc l) K
  have a6 : BlochKatoDuality.adm6 D := fun l _ K => (GlobalTheory.T.tateDual_deRham_and_filZero_dim_all D l K).1
  exact ⟨BlochKatoDuality.ramification_two_and_conjugation_at_q_and_d D a1 a2 a6, BlochKatoDuality.second_proposition_every_localisation D a1 a2 a3 a5 a6⟩

end GlobalTheory.ClosingStatement
