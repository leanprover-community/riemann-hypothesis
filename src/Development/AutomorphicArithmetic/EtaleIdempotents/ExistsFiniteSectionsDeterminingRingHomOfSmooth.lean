module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import GroundTheory.PAdicHodge.LogPowSeries

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

theorem UpperTheory.exists_finite_sections_determining_ringHom_of_smooth :
    ∀ {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)), Smooth q →
        ∀ {V : Y.Opens} (hV : IsAffineOpen V),
        ∃ (k : ℕ) (x : Fin k → Γ(Y, V)), ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
          ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂ := by
  intro O _ Y q hq V hV
  have hlft : LocallyOfFiniteType q := inferInstance
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of O)).Opens) := isAffineOpen_top _
  have hle : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hψ : (q.appLE ⊤ V hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q hlft ⟨⊤, htop⟩ ⟨V, hV⟩ hle
  let ι : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hι : Function.Surjective ι :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2
  let φ : O →+* Γ(Y, V) := (q.appLE ⊤ V hle).hom.comp ι
  have hφ : φ.FiniteType := hψ.comp (RingHom.FiniteType.of_surjective ι hι)
  letI : Algebra O Γ(Y, V) := φ.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, V) := hφ
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s.card, fun i => (s.equivFin.symm i : Γ(Y, V)), ?_⟩
  intro R _ f₁ f₂ hpt hgen
  have hcomp : f₁.comp (q.appLE ⊤ V hle).hom = f₂.comp (q.appLE ⊤ V hle).hom := by
    have e : ∀ f : Γ(Y, V) →+* R, ptOf hV R f ≫ q =
        Spec.map (CommRingCat.ofHom (f.comp (q.appLE ⊤ V hle).hom)) ≫ htop.fromSpec := by
      intro f
      unfold ptOf
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q htop hV hle, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    rw [e, e] at hpt
    have h1 := Spec.map_injective ((cancel_mono htop.fromSpec).1 hpt)
    exact congrArg CommRingCat.Hom.hom h1
  have hO : ∀ a : O, f₁ (algebraMap O Γ(Y, V) a) = f₂ (algebraMap O Γ(Y, V) a) := fun a =>
    congrArg (fun g : Γ(Spec (CommRingCat.of O), ⊤) →+* R => g (ι a)) hcomp
  have hx : ∀ a ∈ s, f₁ a = f₂ a := fun a ha => by
    have := hgen (s.equivFin ⟨a, ha⟩)
    simpa using this
  ext a
  have ha : a ∈ Algebra.adjoin O (s : Set Γ(Y, V)) := by rw [hs]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem b hb => exact hx b hb
  | algebraMap r => exact hO r
  | add b c _ _ hb hc => rw [map_add (f := _), map_add (f := _), hb, hc]
  | mul b c _ _ hb hc => rw [map_mul, map_mul, hb, hc]
