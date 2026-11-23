module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayFlatProjRep
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMemVanIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FlatFamily


open MvPolynomial in
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
  have hh : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro G ⟨hG, -⟩
    exact ⟨d, (mem_homogeneousSubmodule d G).2 hG⟩
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem (h := hh) (p := F)).1 hF e


theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  apply GlobalTheory.ZM.NearCut.eval₂_eq_zero_of_forms_le <;> assumption

theorem exists_flat_projRep_vanIdeal : ∀ (R σ Hh : Type) [CommRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), Ideal (MvPolynomial σ K) → Prop), (∀ (K : Type) [Field K] (x : R →+* K) I, G K x I → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p h i))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : _), RingHom.ker x = q ∧ G K x I} → ∃ (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d p) Z.hom M th ∧ IsProjOver Z.hom ∧ Flat Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), G K x I → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ p Q d G hG hVD
  classical
  have bc : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := fun R R' σ _ _ φ I Z Z' s s' π M th h hpb => RepBC.projRep_baseChange R R' σ φ I Z Z' s s' π M th h hpb
  obtain ⟨hproj, hfg, hbase⟩ := GlobalTheory.FamAlg.forms_through_points R σ Hh p Q d _ hVD (by
    rintro q ⟨K, _, x, I, rfl, hGx⟩
    exact ⟨K, _, x, I, rfl, (hG K x I hGx).2⟩)
  have hhom : ∀ F ∈ vanIdeal d p, ∀ e, MvPolynomial.homogeneousComponent e F ∈ vanIdeal d p :=
    fun F hF e => homogeneousComponent_mem_vanIdeal d p F hF e
  obtain ⟨Z₀, s, M, th, -, hrep, hlfp, hflat⟩ := GlobalTheory.ProjFlat.exists_projRep_flat R σ (vanIdeal d p) d hhom
  have hZ := GlobalTheory.ZM.projRep_projective_ample R σ (vanIdeal d p) (Over.mk s) M th hrep
  refine ⟨Over.mk s, M, th, hrep, hZ.1, hflat (fun e he => by haveI := hproj e he; infer_instance), hlfp hfg, ?_⟩
  intro K _ x I' X s' M' th' hGx hrep'
  obtain ⟨hI'hom, hcut⟩ := hG K x I' hGx
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hsec₁⟩ := bc R K σ x (vanIdeal d p) Z₀ (pullback s (spMap x)) s
    (pullback.snd s (spMap x)) (pullback.fst s (spMap x)) M th hrep hpb
  rw [hbase K x] at hrep₁
  have heqv : ∀ (R' : Type) [CommRing R'] (β : K →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ →
      ((∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) ↔
        ∀ F ∈ vanIdeal d (fun h i => x (p h i)), MvPolynomial.eval₂ β v F = 0) := by
    intro R' _ β v hv
    constructor
    · intro h
      exact eval₂_eq_zero_of_forms_le (fun F hF e => homogeneousComponent_mem_vanIdeal d _ F hF e)
        (fun e he F hFe hF => ((hcut e he).2 F hFe).2 hF) β v hv h
    · intro h
      exact eval₂_eq_zero_of_forms_le hI'hom (fun e he F hFe hF => ((hcut e he).2 F hFe).1 hF) β v hv h
  obtain ⟨e, hes, hlb, hsc⟩ := GlobalTheory.RepUniq.exists_iso_of_projRep K σ I' _ X _ s' _ M' _ th' th₁ hrep' hrep₁ heqv
  have hsc' : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ e.hom ≫ pullback.fst s (spMap x)) w := by
    intro T _ y w
    rw [hsc, hsec₁, Category.assoc]
  have hsame : GlobalTheory.RepUniq.Same M' th' (𝟙 X) M th (e.hom ≫ pullback.fst s (spMap x)) := by
    refine GlobalTheory.RepUniq.same_of_local fun t => ?_
    obtain ⟨W, hW, j, hj, htW, hW'⟩ := GlobalTheory.RepUniq.exists_affine_secCoord hrep'.1 th' (𝟙 X) t
    refine ⟨W, htW, ?_⟩
    have h1 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep'.1 hW'
    have h2 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep.1 ((hsc' _ _ _).1 hW')
    have h3 := (h1.same h2).comp hW.isoSpec.hom
    have h4 : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := GlobalTheory.RepUniq.isoSpec_hom_fromSpec hW
    simp only [Category.comp_id, ← Category.assoc, h4] at h3 ⊢
    exact h3
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, GlobalTheory.RepUniq.lbIso_of_same hrep' hsame, hsc'⟩
  · have sq1 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hes, Category.comp_id]⟩
    simpa using sq1.paste_horiz hpb

end GlobalTheory.ZM.FlatFamily
