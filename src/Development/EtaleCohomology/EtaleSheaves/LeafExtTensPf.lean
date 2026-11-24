module

public import Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExtTensPf

theorem res_isKInjective (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res; infer_instance

theorem res_injective (R : Type) [CommRing R] (F : Shv R) (n : ℤ) : Injective ((res R F).X n) := by
  unfold res
  rw [InjectiveResolution.cochainComplex]
  by_cases h : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ hk).symm inferInstance
  · push_neg at h
    exact (HomologicalComplex.isZero_extend_X _ _ n h).injective

section
variable {C : Type*} [Category C] [Abelian C]

theorem exact_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [∀ n, Mono (ι.f n)] [∀ n, Injective (L.X n)]
    (u : S ⟶ L) (g0 : T ⟶ L) (H : Homotopy u (ι ≫ g0)) : ∃ g : T ⟶ L, ι ≫ g = u := by
  let h' : ∀ i j, T.X i ⟶ L.X j := fun i j => Injective.factorThru (H.hom i j) (ι.f i)
  have hh : (fun i j => ι.f i ≫ h' i j) = H.hom := by
    funext i j; exact Injective.comp_factorThru _ _
  refine ⟨g0 + Homotopy.nullHomotopicMap h', ?_⟩
  rw [Preadditive.comp_add, Homotopy.comp_nullHomotopicMap, hh]
  ext n
  rw [H.comm n]
  simp only [HomologicalComplex.add_f_apply]
  change _ + (dNext n H.hom + prevD n H.hom) = _
  abel

theorem homotopy_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [QuasiIso ι] [L.IsKInjective]
    (u : S ⟶ L) : ∃ g0 : T ⟶ L, Nonempty (Homotopy u (ι ≫ g0)) := by
  let _ := HasDerivedCategory.standard C
  let qt := (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  have hi : IsIso (DerivedCategory.Qh.map (qt.map ι)) := by
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality ι
    have : IsIso (DerivedCategory.Q.map ι) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    have e2 : DerivedCategory.Qh.map (qt.map ι) = (DerivedCategory.quotientCompQhIso C).hom.app S ≫
        DerivedCategory.Q.map ι ≫ (DerivedCategory.quotientCompQhIso C).inv.app T := by
      simp only [Functor.comp_map] at e
      rw [← reassoc_of% e]; simp [qt]
    rw [e2]; infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) L).surjective
    (inv (DerivedCategory.Qh.map (qt.map ι)) ≫ DerivedCategory.Qh.map (qt.map u))
  obtain ⟨g0, rfl⟩ := qt.map_surjective g
  refine ⟨g0, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) L).injective
  rw [Functor.map_comp, Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

theorem extAlongQIso {S T L : CochainComplex C ℤ} (ι : S ⟶ T) (hm : ∀ n, Mono (ι.f n)) (hq : QuasiIso ι)
    (hk : L.IsKInjective) (hinj : ∀ n, Injective (L.X n)) (u : S ⟶ L) : ∃ g : T ⟶ L, ι ≫ g = u := by
  obtain ⟨g0, ⟨H⟩⟩ := homotopy_lift ι u
  exact exact_lift ι u g0 H
end

def LeafTensMono : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ n, Mono (ι.f n)

def LeafTensQIso : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  QuasiIso ι

theorem LeafExtTens_of (hmono : LeafTensMono) (hqiso : LeafTensQIso) : LateralTheory.E.LeafPairExtPf2.LeafExtTens := by
  intro q _ i S T σ τ hσ hτ ι hι u
  exact extAlongQIso ι (hmono q i σ τ hσ hτ ι hι) (hqiso q i σ τ hσ hτ ι hι) (res_isKInjective _ _)
    (res_injective _ _) u

end LateralTheory.E.LeafExtTensPf
