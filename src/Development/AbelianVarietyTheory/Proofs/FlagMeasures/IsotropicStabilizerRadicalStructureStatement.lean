module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isotropicStabilizerRadical_structure : ∀ k r : ℕ, (∀ (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ), (∀ a : Fin r, pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ (∀ j : Fin (k + 1), pEl k r B S *ᵥ bvec (wI k r j) = bvec (wI k r j) - ∑ b, herm (Hb k) (bvec j) (B b) • bvec (eI k r b)) ∧ (∀ b : Fin r, pEl k r B S *ᵥ bvec (esI k r b) = bvec (esI k r b) + (∑ j, B b j • bvec (wI k r j)) + ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • bvec (eI k r a)) ∧ (Sᴴ = -S → pEl k r B S ∈ Nset k r ∧ (pEl k r B S)⁻¹ = pEl k r (-B) (-S))) ∧ (∀ (s : UT r → ℂ) (t : Fin r → ℝ), (skewM s t)ᴴ = -skewM s t) ∧ (∀ S : Matrix (Fin r) (Fin r) ℂ, Sᴴ = -S → ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2) ∧ (∀ B B' (S S' : Matrix (Fin r) (Fin r) ℂ), pEl k r B S * pEl k r B' S' = pEl k r (B + B') (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2)) ∧ ∀ m ∈ UH (Hb k), mEmb k r m ∈ GG k r ∧ (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  first | exact @GlobalTheory.Amp.Rad.radical | exact GlobalTheory.Amp.Rad.radical | (intros; apply GlobalTheory.Amp.Rad.radical <;> assumption)
