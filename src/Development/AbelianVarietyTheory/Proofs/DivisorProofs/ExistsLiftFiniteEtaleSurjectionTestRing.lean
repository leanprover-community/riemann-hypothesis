module

public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory

theorem exists_lift_finiteEtale_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  intro Y Z π hfin het hsurj K _ p x
  let P := pullback π x
  let f : P ⟶ Sp p.R := pullback.snd π x
  have : IsFinite f := inferInstance
  have : Etale f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine P := isAffine_of_isAffineHom f
  let g : Spec Γ(P, ⊤) ⟶ Spec (CommRingCat.of p.R) := P.isoSpec.inv ≫ f
  let φ : CommRingCat.of p.R ⟶ Γ(P, ⊤) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hg_et : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hg_surj : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hφet : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg_et
  have hφff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, hg_surj⟩
  letI : Algebra p.R Γ(P, ⊤) := φ.hom.toAlgebra
  have hBet : Algebra.Etale p.R Γ(P, ⊤) := hφet
  have hBff : Module.FaithfullyFlat p.R Γ(P, ⊤) := hφff
  have hpred : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hBred : _root_.IsReduced Γ(P, ⊤) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced p.R Γ(P, ⊤)
  letI : Algebra K Γ(P, ⊤) := (φ.hom.comp (algebraMap K p.R)).toAlgebra
  haveI : IsScalarTower K p.R Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType K Γ(P, ⊤) := Algebra.FiniteType.trans (S := p.R) inferInstance inferInstance
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType K Γ(P, ⊤))
  have hrad : (RingHom.ker s).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2
    (isReduced_of_injective (Ideal.kerLiftAlg s) (Ideal.kerLiftAlg_injective s))
  let q : TRing K := ⟨n, RingHom.ker s, hrad⟩
  let e : q.R ≃ₐ[K] Γ(P, ⊤) := Ideal.quotientKerAlgEquivOfSurjective hs
  let φK : p.R →ₐ[K] Γ(P, ⊤) := { φ.hom with commutes' := fun _ => rfl }
  let ι : p.R →ₐ[K] q.R := e.symm.toAlgHom.comp φK
  refine ⟨q, ι, ?_, ?_⟩
  · letI := ι.toRingHom.toAlgebra
    let e' : Γ(P, ⊤) ≃ₐ[p.R] q.R := AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) (fun _ => rfl)
    exact ⟨Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm.toLinearEquiv, Algebra.Etale.of_equiv e'⟩
  · refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ P.isoSpec.inv ≫ pullback.fst π x, ?_⟩
    have hι : CommRingCat.ofHom ι.toRingHom = φ ≫ CommRingCat.ofHom e.symm.toRingHom := rfl
    rw [Category.assoc, Category.assoc, pullback.condition]
    change _ ≫ g ≫ x = _
    rw [← hφ, ← Category.assoc, ← Spec.map_comp, ← hι]

end GlobalTheory
