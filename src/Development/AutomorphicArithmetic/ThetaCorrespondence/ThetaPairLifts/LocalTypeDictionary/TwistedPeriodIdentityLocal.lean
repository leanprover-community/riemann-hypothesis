module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section
namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
namespace CompanionTheory.Member.ThetaDownProjection
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
open GlobalTheory.ChainEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
end CompanionTheory.Member.ThetaDownProjection
theorem CompanionTheory.Member.twisted_period_identity_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  intro hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t x hx
  rw [← ch.cv.thDn_w s.core.chain]
  exact CompanionTheory.Member.ThetaDownProjection.proj_thDn hP.cuspRapidDecay s.core t x hx _
end
end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  first | exact @_root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local | exact _root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local | (intros; apply _root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local <;> assumption)
end
end

section
open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  first | exact @_root_.GlobalTheory.Adopt.twisted_period_identity | exact _root_.GlobalTheory.Adopt.twisted_period_identity | (intros; apply _root_.GlobalTheory.Adopt.twisted_period_identity <;> assumption)
end
