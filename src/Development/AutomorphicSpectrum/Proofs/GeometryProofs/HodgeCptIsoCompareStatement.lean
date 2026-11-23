module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hodge_cpt_iso_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (e : A'.X ≅ A.X) (φ : A.Li ≃ₗ[Ω] A'.Li) (Fl : A.Flag) (Fl' : A'.Flag) (τ τ' : CMType H) (i : Fin (D.p + D.q)) (e₀ e₀' : Ω) (L L' : HermLine ι), Birational y → A'.ξ ≫ e.hom = A.ξ → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li), (v ∈ A.V (.inl τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inl τ') q) ∧ (v ∈ A.V (.inr τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inr τ') q)) → (∀ k, (flagStep Ω (Fl.b (.inl τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inl τ')) k ∧ (flagStep Ω (Fl.b (.inr τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inr τ')) k) → (∀ z : Sp ℂ ⟶ A'.X, (A'.Interior z ↔ A.Interior (z ≫ e.hom)) ∧ (A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), A.M.GramAt A.t.PP.L (z ≫ e.hom) b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ)) → (Fl.rootLat (τ, i)).IsDegOn Set.univ y L.a e₀ → (Fl'.rootLat (τ', i)).IsDegOn Set.univ y L'.a e₀' → Fl.IsHodgeLine (τ, i) e₀ L → Fl'.IsHodgeLine (τ', i) e₀' L' → (∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef) → IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z} L L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | exact GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso <;> assumption)
