module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShiftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPointStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartConst

theorem lieMult_constant_along_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X) (P : AbPart 𝔐.t z), ∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult P.tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult P.tB.act (spMap g) τ q') := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P
  obtain ⟨ρ, hρ, hdet⟩ := GlobalTheory.T.exists_sqrt_neg_disc_point E H D l Xo c Y S Ω K J y 𝔐 L z
  obtain ⟨r, hr⟩ := GlobalTheory.T.abelian_part_lie_mult_shift E H 𝔐.X 𝔐.t L z P
  refine ⟨ρ, D.p - r, D.q - r, hρ, fun k _ _ g τ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := (hdet k g τ).1 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.p).mpr h1
    exact (hr k g τ D.p h2).2
  · have h1 := (hdet k g τ).2 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.q).mpr h1
    exact (hr k g τ D.q h2).2

end GlobalTheory.CompanionTheory.Ar.AbPartConst
