module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegrality
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

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  first | exact @GlobalTheory.MomTrans.latInt_translate | exact GlobalTheory.MomTrans.latInt_translate | (intros; apply GlobalTheory.MomTrans.latInt_translate <;> assumption)
