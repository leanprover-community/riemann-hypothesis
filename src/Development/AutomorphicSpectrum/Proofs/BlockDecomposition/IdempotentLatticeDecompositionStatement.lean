module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLatticeDecomposition
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.idempotent_lattice_decomposition : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) → (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 → (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) → (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | exact GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs | (intros; apply GlobalTheory.CompanionTheory.TorusCh.isotropicIdempotent_signs <;> assumption)
