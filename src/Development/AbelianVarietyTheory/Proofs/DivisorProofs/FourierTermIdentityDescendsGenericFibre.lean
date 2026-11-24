module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatEpiLiftRaynaudExtensionFractionPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TermDescend

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ₀ σ₁ σ₂ : Q.SecB k α) (τ₀ τ₁ τ₂ : SecM Y.q.left Q.P.L k) (a b : R), IsTerm Y k α σ₀ τ₀ → IsTerm Y k α σ₁ τ₁ → IsTerm Y k α σ₂ τ₂ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ₀ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval τ₁ r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval τ₂ r z J) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ₀ (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) * sval σ₁ (DegPre.prB Q (FractionRing R)).left z J + gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ₀ σ₁ σ₂ τ₀ τ₁ τ₂ a b h₀ h₁ h₂ H z J hJ
  obtain ⟨Z, p, w, y, hw, hp, hinj, hy⟩ := GlobalTheory.RayLift.exists_flat_lift R Q O oa Y z
  subst hw
  obtain ⟨J', hJ', hJJ⟩ := exists_good Q.P.L Q.P.isLB w (K := (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left)
    (fun ψ => p ≫ ψ) J (fun ψ ψ' e => by rw [(cancel_epi p).1 e]) (fun ψ => by
      rw [Scheme.Hom.comp_apply]; exact hJ ψ)
  have hfun : (fun ψ => J' (p ≫ ψ)) = J := funext hJJ
  let T : Over (Sp R) := Over.mk (y ≫ Y.H.hom)
  let x : T ⟶ Y.H := Over.homMk y rfl
  let v : (Z.presheaf.stalk w)ˣ := val ((Y.Φ T x).s α) (𝟙 _) w J'
  have e₀ : sval τ₀ y w J' = sval σ₀ (y ≫ Y.q.left) w J' * v.val := h₀ T x w J' hJ'
  have e₁ : sval τ₁ y w J' = sval σ₁ (y ≫ Y.q.left) w J' * v.val := h₁ T x w J' hJ'
  have e₂ : sval τ₂ y w J' = sval σ₂ (y ≫ Y.q.left) w J' * v.val := h₂ T x w J' hJ'
  have E := H Z y w J' hJ'
  have hH : y ≫ Y.H.hom = p ≫ ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) := by
    rw [← Category.assoc, ← hy, Category.assoc, Over.w Y.q]
  rw [e₀, e₁, e₂, ← _root_.mul_assoc, ← _root_.mul_assoc, ← add_mul] at E
  have E' := (Units.mul_left_inj _).1 E
  rw [hH, hy, GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ',
    GlobalTheory.HeatDefect.sval_comp_stalk _ _ _ _ hJ', GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial,
    GlobalTheory.HeatDefect.gs_comp_stalk p _ w ⊤ trivial, hfun, ← map_mul, ← map_mul, ← map_add] at E'
  exact hinj E'

end GlobalTheory.TermDescend
