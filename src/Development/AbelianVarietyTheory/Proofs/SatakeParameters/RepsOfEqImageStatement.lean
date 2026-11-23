module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImage
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.xiL_two_alt : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  first | exact @GlobalTheory.TwU.XiTwo.xiL_two | exact GlobalTheory.TwU.XiTwo.xiL_two | (intros; apply GlobalTheory.TwU.XiTwo.xiL_two <;> assumption)
