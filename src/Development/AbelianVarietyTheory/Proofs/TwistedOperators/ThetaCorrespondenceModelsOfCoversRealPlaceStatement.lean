module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → (∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ)) → PairLaw a₁ a₂ R₁ R₂ (blattner l₁) (blattner l₂) → LiftLaw M τ A pt N B := by
  first | exact @GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | exact GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | (intros; apply GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw <;> assumption)
