module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
open GlobalTheory.EtC.FreeHom in

theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections :
    ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R),
      (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧
      (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U,
        (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
          φ V (P.map g.op x) = Sec.res g (φ U x)) →
        ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧
      (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
        val s V (P.map g.op x) = Sec.res g (val s U x)) ∧
      (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x,
        val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧
      (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x,
        val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧
      ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x,
        val (s + s') U x = val s U x + val s' U x ∧
        val (m • s) U x = m • val s U x := by
  intro R _ P G
  have evaluate {Q : PSh} {F : Shv R} (s : (free R).obj Q ⟶ F)
      (U : Scheme.{0}) (x : Q.obj (op U)) :
      val s U x =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up x)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s s' h
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ G.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    have hx := h U.unop x
    rw [evaluate, evaluate] at hx
    exact hx
  · intro φ hφ
    refine ⟨desc P G φ hφ, ?_⟩
    intro U x
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom =
        descP P G φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply (descP P G φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  · intro s V U g x
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (G.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    rw [← freePresheaf_map_freeMk P g.op x]
    exact congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)
  · intro P' f s U x
    rw [evaluate, evaluate]
    have h : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom =
        (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
      (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
    rw [h]
    change ((toSheafify _ _ ≫ s.hom).app (op U)).hom
      ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
    rw [freePresheaf_map_app_freeMk]
  · intros
    rfl
  · intro s s' m U x
    let evaluation : ((free R).obj P ⟶ G) →+ Sec G U :=
      AddMonoidHom.mk' (fun t => val t U x) (fun _ _ => rfl)
    exact ⟨rfl, map_zsmul evaluation m s⟩
