module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapSign_eq_eta_gramDet | exact GlobalTheory.KapLat.kapSign_eq_eta_gramDet | (intros; apply GlobalTheory.KapLat.kapSign_eq_eta_gramDet <;> assumption)
