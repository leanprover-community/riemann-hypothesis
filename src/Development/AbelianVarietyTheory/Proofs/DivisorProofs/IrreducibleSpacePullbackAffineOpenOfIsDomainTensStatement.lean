module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct


set_option backward.isDefEq.respectTransparency false in

theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    (letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f))) := by
  intro F _ X g V hV k _ f
  let : Algebra F Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let : Algebra F k := f.toAlgebra
  intro hdom
  have hSpec : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hComp : V.ι ≫ g = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← hSpec, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  let m := pullback.map (V.ι ≫ g) (spMap f) (Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap F k))) hV.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hComp]) (by simp only [Category.comp_id, Category.id_comp]; rfl)
  let e : pullback (V.ι ≫ g) (spMap f) ≅ Spec (CommRingCat.of (Γ(X, V) ⊗[F] k)) :=
    asIso m ≪≫ pullbackSpecIso F Γ(X, V) k
  have : IsDomain (Γ(X, V) ⊗[F] k) :=
    MulEquiv.isDomain (k ⊗[F] Γ(X, V)) (Algebra.TensorProduct.comm F Γ(X, V) k).toRingEquiv.toMulEquiv
  have : IrreducibleSpace (Spec (CommRingCat.of (Γ(X, V) ⊗[F] k))) :=
    PrimeSpectrum.irreducibleSpace (R := Γ(X, V) ⊗[F] k)
  exact Function.Surjective.irreducibleSpace e.inv.homeomorph.continuous e.inv.homeomorph.surjective
