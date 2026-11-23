module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjectiveStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC


open GlobalTheory.EtC.MuTw in
theorem GlobalTheory.EtC.tw_one_mu : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  intro q _
  have hunit : ∀ (C : Type) [CommRing C], IsUnit (q : C) → IsUnit (q : Γ(Spec (CommRingCat.of C), ⊤)) := by
    intro C _ hC
    have := hC.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simpa using this
  let e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C) :=
    fun C _ hC =>
      ((AddEquiv.ofBijective ((etaS q).hom.app (op (Spec (CommRingCat.of C)))).hom.toAddMonoidHom
        ⟨GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q _ (hunit C hC), GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective q _ (hunit C hC)⟩).trans AddEquiv.ulift).trans
        (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv q).toAdditive
  refine ⟨e, ?_⟩
  intro C D _ _ φ hC hD x
  apply Units.ext
  have h1 := etaS_res q (Spec.map (CommRingCat.ofHom φ)) x
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (muVal q (Sec.map (etaS q) (Sec.res (Spec.map (CommRingCat.ofHom φ)) x))) = φ ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (muVal q (Sec.map (etaS q) x)))
  rw [h1, muVal_res]
  exact congrArg (fun f => f.hom (muVal q (Sec.map (etaS q) x))) h2
