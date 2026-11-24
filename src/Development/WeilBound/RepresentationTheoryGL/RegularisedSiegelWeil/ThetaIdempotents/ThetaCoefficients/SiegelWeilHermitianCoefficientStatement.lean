module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianCoefficient
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

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.siegel_weil_hermitian_coefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (N : ℕ) (Φ : Fin N → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all | exact GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_finset_sum_all <;> assumption)
