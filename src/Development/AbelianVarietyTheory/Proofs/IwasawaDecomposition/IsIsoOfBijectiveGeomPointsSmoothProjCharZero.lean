module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
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
import Mathlib.Tactic.TypeStar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

namespace GlobalTheory.BijPointsIso

universe u

variable {X Y : Scheme.{u}}

theorem universallyInjective_of_injective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro z
  let K := AlgebraicClosure ((pullback f f).residueField z)
  let φ : Spec (.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫
      (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
    h K (by simp only [Category.assoc, pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hφ₁]
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨(φ ≫ pullback.fst f f) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem surjective_of_surjective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Surjective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    Function.Surjective f := by
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨g, hg⟩ := h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
    Y.fromSpecResidueField y)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨g pt, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  simp only at hg
  rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem bijective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (hR : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩
  change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e
  rw [Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot,
    sub_eq_zero] at e
  exact e

theorem isIso_stalkMap_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [UniversallyInjective f] [IsDominant f]
    (hc : CharZero (Y.residueField (f (genericPoint X)))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  set x := genericPoint X
  have h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective.{u} f).out 1 3).mp ‹_›
  have hpi := h3.2 x
  have hr : Function.Bijective (f.residueFieldMap x) := by
    algebraize [(f.residueFieldMap x).hom]
    have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hpi
    exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _
  have hX : IsField (X.presheaf.stalk x) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f x)) := by
    rw [GlobalTheory.apply_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  have hsq := Scheme.residue_residueFieldMap f x
  have hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm
  have bX := bijective_residue_of_isField hX
  have bY := bijective_residue_of_isField hY
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (X.residue x ∘ f.stalkMap x) := by
    have e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x)) := funext hsq'
    rw [e]; exact hr.comp bY
  exact (Function.Bijective.of_comp_iff' bX _).mp this

end GlobalTheory.BijPointsIso

namespace GlobalTheory.BijPointsIso

theorem charZero_residueField {F : Type} [Field F] [CharZero F] (Y : Var F) (y : Y.X) :
    CharZero (Y.X.residueField y) := by
  let ψ : F →+* Y.X.residueField y :=
    (Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))
  exact charZero_of_injective_ringHom ψ.injective

theorem isIso_of_bijective_points : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F)
    (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str →
      (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) →
        IsIso h := by
  intro F _ _ Y₁ Y₂ h hc hb
  have : UniversallyInjective h :=
    universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1
  have : IsProper (h ≫ Y₂.str) := hc ▸ inferInstance
  have : IsProper h := IsProper.of_comp h Y₂.str
  have hs : Function.Surjective h := surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2
  have : IsDominant h := ⟨hs.denseRange⟩
  have := isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)
  have hN := Y₂.isNormalScheme
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk

end GlobalTheory.BijPointsIso
