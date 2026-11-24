module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
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

theorem _root_.GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties : ∀ k r : ℕ, (∀ u u' : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → IsUnit u'.det → uEmb k r (u * u') = uEmb k r u * uEmb k r u') ∧ uEmb k r 1 = 1 ∧ (∀ u : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → uEmb k r u ∈ GG k r ∧ (uEmb k r u)⁻¹ = uEmb k r u⁻¹ ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a)) ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a)) ∧ ∀ w, inWb k r w → uEmb k r u *ᵥ w = w) ∧ (∀ x : UT r → ℂ, (upper x).det = 1 ∧ uEmb k r (upper x) ∈ Nset k r) := by
  first | exact @GlobalTheory.Amp.UEmb.uEmb_hom | exact GlobalTheory.Amp.UEmb.uEmb_hom | (intros; apply GlobalTheory.Amp.UEmb.uEmb_hom <;> assumption)
