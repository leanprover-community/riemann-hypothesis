module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace ReciprocityTheory.AnForm.R.FinalTheorems

noncomputable abbrev reesChart {R : Type u} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) :
    Subalgebra R (Localization.Away (g i)) :=
  Algebra.adjoin R (Set.range fun k => IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)))

def ReesCharts {X W : Scheme.{u}} (π : W ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ∃ (m : ℕ) (g : Fin m → Γ(X, U.1)),
    Ideal.span (Set.range g) = J.ideal U ∧
    ∃ V : Fin m → W.Opens, (⨆ i, V i) = π ⁻¹ᵁ U.1 ∧
      ∀ i, ∃ e : (V i).toScheme ≅ Spec (CommRingCat.of (reesChart g i)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (reesChart g i))) ≫ U.2.fromSpec =
          (V i).ι ≫ π

def LogResStC (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩) ∧
    (∀ x : X, SncAt (Scheme.IdealSheafData.vanishingIdeal B) x →
      ∃ f ∈ nonZeroDivisors (X.presheaf.stalk x), stalkId J x = Ideal.span {f}) ∧
    (∃ U : X.Opens, (U : Set X) = {x : X | SncAt (Scheme.IdealSheafData.vanishingIdeal B) x} ∧
      IsIso (π ∣_ U)) ∧
    IsSeparated π ∧ LocallyOfFiniteType π ∧ ReesCharts π J

def GFLogStCR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

end ReciprocityTheory.AnForm.R.FinalTheorems
