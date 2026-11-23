module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRing
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  first | exact @GlobalTheory.HeatValues.heat_values_at_point | exact GlobalTheory.HeatValues.heat_values_at_point | (intros; apply GlobalTheory.HeatValues.heat_values_at_point <;> assumption)
