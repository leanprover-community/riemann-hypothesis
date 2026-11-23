module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionsUniqueDecomposition
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpThickening

open GlobalTheory.RelConstThickening

theorem existsUnique_affine {R : Type} [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R))
    (p₂ : P ⟶ Z) (H : IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))))
    {V : Z.Opens} (hV : IsAffineOpen V) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := R) (constHom h V) (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]

theorem existsUnique_decomp : ∀ (R : Type) [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R)) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))) → ∀ (O : Z.Opens) (F : Γ(P, p₂ ⁻¹ᵁ O)), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun _ _ _ _ h p₁ p₂ H O F =>
    existsUnique_comb (W := ⊤) (fun _ hV _ F => existsUnique_affine h p₁ p₂ H hV F) O le_top F

end GlobalTheory.SpThickening

end
