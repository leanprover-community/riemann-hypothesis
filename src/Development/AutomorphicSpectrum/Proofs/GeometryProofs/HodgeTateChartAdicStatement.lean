module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartAdic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.hodge_tate_chart_adic : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra R O] (n N : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (D : HTChart R K c p n N Ω) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (u : Fin N → La) (hu : IsPolLattice c p EF u) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) (x : Spec (CommRingCat.of R) ⟶ S) (Γ₀ : QFGroup R (LevGrp La p n)) (i : Γ₀.G.left ⟶ G.left) (hi : Γ₀.IsTorsionAlong G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (act : 𝓞 E → (G ⟶ G)) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n) (ζ₀ : Rˣ) (X : TorsTower p G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) La) (F : (X.Γ n).G.left ⟶ Γ₀.G.left) (L' : Type) [AddCommGroup L'] [Module O L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) L') (ρ' : 𝓞 E →+* Module.End O L') (hρ' : M'.IsActOf act ρ') (ζ : ℕ → Oˣ) (κ : O) (P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L')), IsHTChartOf D Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', D.e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → (X.Γ n).IsBaseChange Γ₀ (algebraMap R O) F → F ≫ i = X.i n → algebraMap R O (ζ₀ : R) = (ζ n : O) → ζ n ^ p ^ n = 1 → IsPointOf p (X.IsDer M') EF ζ ρ' u P → ∃ io : D.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L'), D.ReducesTo (algebraMap R O) P io := by
  exact @GlobalTheory.CompanionTheory.Ar.HT.ChartRed.reducesTo_of_isHTChartOf
