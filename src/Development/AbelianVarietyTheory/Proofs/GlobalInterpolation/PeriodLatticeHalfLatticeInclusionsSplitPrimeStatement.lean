module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.HalfIncl.half_inclusions | exact GlobalTheory.MomT.HalfIncl.half_inclusions | (intros; apply GlobalTheory.MomT.HalfIncl.half_inclusions <;> assumption)
