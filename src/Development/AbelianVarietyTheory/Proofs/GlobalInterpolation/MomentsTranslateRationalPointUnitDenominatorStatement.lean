module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsTranslateRationalPointUnitDenominator
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.moments_translate_rationalPoint_unitDenominator : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  first | exact @GlobalTheory.MomT.UnitTr.moments_unit_translate | exact GlobalTheory.MomT.UnitTr.moments_unit_translate | (intros; apply GlobalTheory.MomT.UnitTr.moments_unit_translate <;> assumption)
