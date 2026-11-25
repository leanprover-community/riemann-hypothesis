module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModel
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_model_point_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG :=
  PositivityTheory.HtPt.Gh.hodge_tate_free_sandwich

end GlobalTheory.CompanionTheory.Ar.HT
