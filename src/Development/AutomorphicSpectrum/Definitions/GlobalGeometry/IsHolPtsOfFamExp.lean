module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GaExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieInh

def ev {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) : Γ(T, ⊤) →+* A :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

private theorem ev_eps_eq_ev {T : Scheme.{0}} (x : Sp (DualNumber ℂ) ⟶ T) (h) (f : Γ(T, ⊤)) :
    GlobalTheory.FibreDeriv.evEps x ⊤ h f = ev x f := by
  have hx : x.appLE ⊤ ⊤ h = x.app ⊤ := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  simp only [GlobalTheory.FibreDeriv.evEps, ev, hx]

theorem valAt'_top {T : Scheme.{0}} (x : Sp ℂ ⟶ T) (f : Γ(T, ⊤)) : valAt' x ⊤ f = ev x f := by
  have hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) = x := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have h1 := GlobalTheory.FibreDeriv.fst_evEps (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x) x hx ⊤ le_rfl f
  rw [← h1, ev_eps_eq_ev]
  have key : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom =
      (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
  have h2 := congrArg (fun g => (g.hom f).fst) key
  simpa [ev, TrivSqZeroExt.algebraMap_eq_inl] using h2

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)}

end GlobalTheory.CompanionTheory.Ar.Flat.GaExp
