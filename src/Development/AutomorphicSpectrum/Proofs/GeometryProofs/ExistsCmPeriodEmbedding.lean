module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PureFamilyDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PurePeriodLocalBasisExistsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraicStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_cmPoint_locBasis_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (τ : E →+* ℂ) (ℓ : Nat.Primes) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → ∃ (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (X : CMPack Z c FU i hP) (v : Vecs X.y D.p) (w : Vecs X.y D.q), k ≤ X.K ∧ IsLocBasis (𝓞 E) ℓ x ∧ X.IsCMFrame τ hx v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z τ ℓ k hk hty hτ
  obtain ⟨P₀, hP₀⟩ := PeriodNonempty.exists_isPeriod E H (FU.Di i) g ty
    (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty)
  have hsum : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨P, hP, x, hloc, hx⟩ := GlobalTheory.T.pure_period_local_basis_exists E H (FU.Di i) g ty P₀ D.p D.q ℓ hP₀ hty hsum
  obtain ⟨hli, n, hn, hspan⟩ := id hloc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (dvd_zero _))
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.pure_family_decomposition E H (FU.Di i) g ty P hP D.p D.q x n hx hspan
  obtain ⟨X, hkX⟩ := GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod E H D l Xo c g ty FU i Z P hP n k hk hn0 hsplit
  obtain ⟨⟨v, w, hvw⟩, -⟩ := GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli
  exact ⟨P, hP, x, hx, X, v, w, hkX, hloc, hvw⟩

end GlobalTheory.CompanionTheory.Ar.Fl
