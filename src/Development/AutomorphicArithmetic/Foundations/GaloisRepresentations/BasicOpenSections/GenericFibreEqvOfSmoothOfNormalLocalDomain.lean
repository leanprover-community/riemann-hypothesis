module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.Gal.Mod.generic_fibre_eqv_of_smooth_of_normal_local_domain : GlobalTheory.EtC.E3 → ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (L : Type) [Field L] [Algebra T L] [IsFractionRing T L] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ), Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T L))))) (tw q i) := by
  intro hE q _ T _ _ _ hA hq L _ _ _ X p _ i
  let e : FractionRing T ≃ₐ[T] L := IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) L
  let gF := Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))
  let u := Spec.map (CommRingCat.ofHom ((e : FractionRing T ≃+* L) : FractionRing T →+* L))
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap T L)) = u ≫ gF := by
    simp only [u, gF, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    simp [e]
  haveI : IsIso u := by
    have : IsIso (CommRingCat.ofHom ((e : FractionRing T ≃+* L) : FractionRing T →+* L)) :=
      (RingEquiv.toCommRingCatIso (e : FractionRing T ≃+* L)).isIso_hom
    infer_instance
  let Φ := pullback.map p (Spec.map (CommRingCat.ofHom (algebraMap T L))) p gF (𝟙 _) u (𝟙 _)
    (by simp) (by rw [hcomp, Category.comp_id])
  have hfst : Φ ≫ pullback.fst p gF = pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T L))) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  obtain ⟨hiso, hc, -, -⟩ := eqv_basic (ZMod q) (tw q i)
  have h1 : Eqv (ZMod q) (sch.map Φ) (tw q i) := hiso _ _ _ inferInstance
  have h2 : Eqv (ZMod q) (sch.map (pullback.fst p gF)) (tw q i) := hE q T hA hq p i
  rw [← hfst, Functor.map_comp]
  exact (hc _ _ _ _ _).1 h1 h2
