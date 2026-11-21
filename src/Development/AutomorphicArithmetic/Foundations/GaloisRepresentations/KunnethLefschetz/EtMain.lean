import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.IntOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PHypEmb
import Development.EtaleCohomology.EtaleTrace.FinLCover
import Development.EtaleCohomology.EtaleTrace.LCompDecPf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Development.EtaleCohomology.EtaleTrace.LCompIntPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLowTL
import Development.EtaleCohomology.EtaleTrace.PtCoverPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.LowLHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTowerL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTwBij
import Development.EtaleCohomology.EtaleTrace.LRingPf
import Development.EtaleCohomology.EtaleTrace.LPdCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.GysinTwistZeroExists
import Mathlib.CategoryTheory.CofilteredSystem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQOnto
import Development.EtaleCohomology.EtaleTrace.LKunnethCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.KunLHolds
import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPtInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDetectL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDualL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinSupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnCls
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTrComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DivLHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PBasisOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTopPart

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.offEx_holds :
    UpperTheory.Gal.KunnethLefschetz.OffEx := by
  refine ⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩
  intro Z' X' Z X ι' ι f u h U hU
  change f ⁻¹' (U : Set X) = _
  rw [hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.pairs_holds :
    UpperTheory.Gal.KunnethLefschetz.Pairs := by
  unfold Pairs
  intro k _ d X p hsep hsm
  have hfst : SmoothOfRelativeDimension d (pullback.fst p p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback p p).flip hsm
  have hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p) :=
    smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p
  have hid : SmoothOfRelativeDimension 0 (𝟙 (S k)) := inferInstance
  refine ⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [pullback.diagonal_fst_assoc]
    exact hsm
  · have h1 : IsClosedImmersion (y.1 ≫ p) := by rw [y.2]; infer_instance
    exact IsClosedImmersion.of_comp y.1 p
  · rw [Nat.zero_add]; exact hsm
  · rw [y.2]; exact hid
  · have key : ∀ s : PullbackCone (slice y) (pullback.diagonal p),
        s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd := by
      intro s
      have c := s.condition
      have c1 := congrArg (· ≫ pullback.fst p p) c
      have c2 := congrArg (· ≫ pullback.snd p p) c
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id] at c1 c2
      exact ⟨c1, c2⟩
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)
    · have e1 : slice y ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
      have e2 : slice y ≫ pullback.snd p p = p ≫ y.1 := pullback.lift_snd _ _ _
      have hy : y.1 ≫ p ≫ y.1 = y.1 := by rw [← Category.assoc, y.2, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    · intro s
      rw [Category.assoc, (key s).2, (key s).1]
    · intro s
      rw [Category.assoc, (key s).2]
    · intro s m h1 _
      rw [← h1, Category.assoc, y.2, Category.comp_id]
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finCov_holds :
    UpperTheory.Gal.KunnethLefschetz.FinCov := by
  unfold UpperTheory.Gal.KunnethLefschetz.FinCov
  intro k _ _ d X p h1 h2 h3
  obtain ⟨π, t, e1, e2, e3, -⟩ := LateralTheory.Fin.LCover.intersectionNumber_baseChange k d p h1 h2 h3
  exact ⟨π, e1, e2, e3⟩
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finFib_holds :
    UpperTheory.Gal.KunnethLefschetz.FinFib := by
  intro k _ _ X Y p r π hπ hfin t U hU
  classical
  obtain ⟨t0, ht0⟩ := t
  change ↑U = (Set.range t0)ᶜ at hU
  have hA : IsLocallyArtinian (pullback π t0) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π t0)
  have hD : DiscreteTopology ↥(pullback π t0) := inferInstance
  have hF : Finite ↥(pullback π t0) := by
    have h := (pullback.snd π t0).finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    refine h.subset fun z _ => ?_
    exact Subsingleton.elim _ _
  haveI : Fintype ↥(pullback π t0) := Fintype.ofFinite _
  let c : ↥(S k) := IsLocalRing.closedPoint k
  let e : ↥(pullback π t0) → (S k ⟶ pullback π t0) := fun z =>
    pointOfClosedPoint (pullback.snd π t0) z (isClosed_discrete _)
  have he : ∀ z, e z ≫ pullback.snd π t0 = 𝟙 _ := fun z => pointOfClosedPoint_comp _ _ _
  have he' : ∀ z, e z c = z := fun z => pointOfClosedPoint_apply _ _ _ _
  let g : ↥(pullback π t0) → Pt p := fun z =>
    ⟨e z ≫ pullback.fst π t0, by
      rw [Category.assoc, ← hπ, ← Category.assoc (pullback.fst π t0), pullback.condition,
        Category.assoc, ht0, Category.comp_id, he]⟩
  refine ⟨Finset.univ.image g, ?_⟩
  unfold OffPts
  rw [Scheme.Hom.coe_preimage, hU, Set.preimage_compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
    refine ⟨g z, ⟨z, rfl⟩, c, ?_⟩
    change (e z ≫ pullback.fst π t0) c = x
    rw [Scheme.Hom.comp_apply, he', hz1]
  · rintro ⟨y, ⟨z, rfl⟩, b, rfl⟩
    refine ⟨(e z ≫ pullback.snd π t0) b, ?_⟩
    change (e z ≫ pullback.snd π t0 ≫ t0) b = (e z ≫ pullback.fst π t0 ≫ π) b
    rw [pullback.condition]
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem comps_holds : Comps := by
  classical
  unfold Comps
  intro k _ _ d X p hp hX
  obtain ⟨hfin, hopen⟩ := comp_fin d p hp
  let m := Nat.card (_root_.ConnectedComponents X)
  let e : Fin m ≃ _root_.ConnectedComponents X := (Finite.equivFin _).symm
  let rep : Fin m → X := fun j => (ConnectedComponents.surjective_coe (e j)).choose
  have hrep : ∀ j, (rep j : _root_.ConnectedComponents X) = e j := fun j =>
    (ConnectedComponents.surjective_coe (e j)).choose_spec
  let U : Fin m → X.Opens := fun j => ⟨connectedComponent (rep j), hopen _⟩
  have hUc : ∀ j, IsClosed (U j : Set X) := fun j => isClosed_connectedComponent
  have hmem : ∀ j (x : X), x ∈ (U j : Set X) ↔ e j = (x : _root_.ConnectedComponents X) := by
    intro j x
    rw [← hrep]
    exact ⟨fun h => ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq h),
      fun h => by
        have := ConnectedComponents.coe_eq_coe.mp h
        show x ∈ connectedComponent (rep j)
        rw [this]; exact mem_connectedComponent⟩
  refine ⟨m, U, fun j => ?_, fun x => ?_, fun j j' hj => ?_⟩
  · have h2 := clopen_smoothProper_projective d p hp hX (U j) (hUc j)
    have hc : ConnectedSpace (U j) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact ⟨h2.1, h2.2, LCompInt_of k d ((U j).ι ≫ p) h2.1 hc⟩
  · refine ⟨e.symm (x : _root_.ConnectedComponents X), ?_⟩
    show x ∈ (U _ : Set X)
    rw [hmem]
    exact e.apply_symm_apply _
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact (hj (e.injective (((hmem j x).mp hx.1).trans ((hmem j' x).mp hx.2).symm))).elim

end UpperTheory.Gal.KunnethLefschetz
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sec_of {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ S k) (hf : Etale f)
    (hs : Surjective f) : ∃ s : S k ⟶ Y, s ≫ f = 𝟙 _ := by
  have hmem : Sieve.generate (Presieve.singleton f) ∈ Scheme.etaleTopology (S k) := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨y, rfl⟩ := hs.surj u
    exact ⟨Y, f, y, hf, rfl, ⟨Y, 𝟙 Y, f, Presieve.singleton.mk, Category.id_comp f⟩⟩
  obtain ⟨Z, h, g, hg, hcomp⟩ := PtCover_of k _ hmem
  cases hg
  exact ⟨h, hcomp⟩

theorem ptVanT_holds : PtVanT := by
  intro hIn k _ _ q n i hn
  have hzero : ∀ x : Ht q (sch.obj (S k)) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hIn.a5 (ZMod q) (S k) (tw q i) n hn x
    obtain ⟨s, hsf⟩ := sec_of f hf hs
    calc x = pull (ZMod q) (𝟙 (sch.obj (S k))) (tw q i) n x := (pull_id _ _ _ _ x).symm
      _ = pull (ZMod q) (sch.map s ≫ sch.map f) (tw q i) n x := by
        rw [← CategoryTheory.Functor.map_comp, hsf, CategoryTheory.Functor.map_id]
      _ = pull (ZMod q) (sch.map s) (tw q i) n (pull (ZMod q) (sch.map f) (tw q i) n x) :=
        pull_comp _ _ _ _ _ x
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem sub_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (q : ℕ) (n i : ℤ)
    (h : Subsingleton (Ht q (sp A) n i)) : Subsingleton (Ht q (sp B) n i) := by
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
      ext x
      simp
    rw [this]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) := by
    rw [← pull_comp, hid, pull_id]
  have hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y) := by
    rw [← pull_comp, hid, pull_id]
  rw [hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)
    (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]

theorem UpperTheory.Gal.KunnethLefschetz.affVan_holds :
    UpperTheory.Gal.KunnethLefschetz.AffVan := by
  intro hIn hPt k _ _ q _ hq d n i hn
  show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)
  induction d with
  | zero =>
    have h0 : Subsingleton (Ht q (sp k) n i) := hPt hIn k q n i hn
    exact sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0
  | succ d ih =>
    have hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k) := by
      have := hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)
      rwa [map_natCast] at this
    have hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i) := by
      have hb := hIn.c4 q (MvPolynomial (Fin d) k) hq' i n
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hb.2 x
      obtain ⟨b, rfl⟩ := hb.2 y
      rw [Subsingleton.elim a b]
    exact sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private def castHom {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht q E n i →+ Ht q E n' i' where
  toFun := Ht.cast hn hi
  map_zero' := by subst hn hi; rfl
  map_add' := LRingPf.cast_add hn hi

private def pairSP {k : Type} [Field k] {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h : IsPair d e p ι) : LateralTheory.CohomologicalPurity.SP d :=
  { X := X, Z := Z, S := S k, p := p, ι := ι, e := e
    U := ⟨(Set.range ι)ᶜ, (h.cl.base_closed.isClosed_range).isOpen_compl⟩
    cl := h.cl, smX := h.big, smZ := h.small, hU := rfl }

theorem UpperTheory.Gal.KunnethLefschetz.gysTL_holds :
    UpperTheory.Gal.KunnethLefschetz.GysTL := by
  unfold GysTL
  intro hI hO k _
  have hg : ∀ d, LateralTheory.CohomologicalPurity.Gysin d := hI.gys
  unfold LateralTheory.CohomologicalPurity.Gysin at hg
  choose gys rs H using hg
  refine ⟨⟨fun q d e Z X p ι h n m i j hn hi =>
    (castHom hn hi).comp (gys d q (pairSP h) n i), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    exact ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.2
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU hs
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    have hx := ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.1
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨u, rfl⟩ := (hx a).1 ha
    rw [hs.elim u 0]
    exact map_zero (rs d q (pairSP h) n i)
  · intro q _ hq d e' e Z' X' Z X p' ι' p ι h' h f u hpb n m i j hn hi a
    subst hn hi
    have hoff : Off ι' (f ⁻¹ᵁ (pairSP h).U) := hO.2 ι' ι f u hpb (pairSP h).U rfl
    have hle : (pairSP h').U ≤ f ⁻¹ᵁ (pairSP h).U :=
      (TopologicalSpace.Opens.ext hoff.symm : (pairSP h').U = f ⁻¹ᵁ (pairSP h).U).le
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.1 (pairSP h') ⟨f, u, hpb, hle⟩ n i).1 a)
  · intro q _ hq d e Z X p ι h n m r s t i j i' j' w h1 h2 h3 h4 k1 k2 k3 k4 a b
    subst h1 h2 h3 k1 k2 k3
    exact (H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.1 n m i j a b
  · intro q r _ hq hr d e Z X p ι h n m i j hn hi a
    subst hn hi
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.2 r hr n i).1 a).symm
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem qEasy_holds : QEasy := by
  unfold QEasy
  intro l _ k _ G
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  refine ⟨?_, ?_, ?_⟩
  · intro d e Z X p ι h n m hn U hU a
    have h0 : (pullHl l (sch.map U.ι) m 0).comp (G.hl h hn) = 0 :=
      LinearMap.ext fun x => Subtype.ext (funext fun j =>
        (G.exact j h hn U hU _).mpr ⟨x.1 j, rfl⟩)
    have h1 : (pb l U.ι m).comp (G.q h hn) = 0 := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero]
    exact LinearMap.congr_fun h1 a
  · intro d e Z X p ι h n m hn U hU hs
    have hinj : Function.Injective (G.hl h hn) := fun x y hxy =>
      Subtype.ext (funext fun j => G.inj j h hn U hU (hs j) (congrArg (fun z => z.1 j) hxy))
    unfold Gys0.q
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro d e' e Z' X' Z X p' ι' p ι h' h f u hf hp n m hn a
    have h0 : (pullHl l (sch.map f) m 0).comp (G.hl h hn) =
        (G.hl h' hn).comp (pullHl l (sch.map u) n 0) :=
      LinearMap.ext fun x => Subtype.ext (funext fun j => G.nat j h' h f u hf hp hn (x.1 j))
    have h1 : (pb l f m).comp (G.q h hn) = (G.q h' hn).comp (pb l u n) := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h0]
    exact LinearMap.congr_fun h1 a

end UpperTheory.Gal.KunnethLefschetz
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.limOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.LimOnto := by
  intro A B _ ra rb f hf z hz hsurj
  let F : ℕ → Type 1 := fun j => {a : A j // f j a = z j}
  let g : ∀ n, F (n + 1) → F n := fun n a =>
    ⟨ra n a.1, by rw [← hf, a.2, hz]⟩
  let G : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := F) (fun n => TypeCat.ofHom (g n))
  haveI : ∀ j : ℕᵒᵖ, Finite (G.obj j) := fun j => (inferInstance : Finite (F j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (G.obj j) := fun j => by
    obtain ⟨a, ha⟩ := hsurj j.unop
    exact ⟨(⟨a, ha⟩ : F j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system G
  refine ⟨fun j => (s (Opposite.op j) : F j).1, fun j => ?_, fun j => (s (Opposite.op j) : F j).2⟩
  have h1 := hs (homOfLE (Nat.le_succ j)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h1
  have h2 := congrArg Subtype.val h1
  exact h2
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem qProj_holds : QProj := by
  unfold QProj
  intro hI l _ k _ G d e Z X p ι h n m r s t h1 h2 h3 h4 a b
  have key : ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj Z) m 0),
      G.q h h2 (cupV l Z h1 (pb l ι n ((1 : ℚ_[l]) ⊗ₜ x)) ((1 : ℚ_[l]) ⊗ₜ y)) =
        cupV l X h4 ((1 : ℚ_[l]) ⊗ₜ x) (G.q h h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
    intro x y
    rw [LRingPf.pb_tmul, LRingPf.cupV_eq l hI.a11 Z, LRingPf.cupV_eq l hI.a11 X, LRingPf.cupQ_tmul]
    simp only [Gys0.q, LinearMap.baseChange_tmul]
    rw [LRingPf.cupQ_tmul]
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    exact G.proj j h h1 h2 h3 h4 (x.1 j) (y.1 j)
  have hfg : ((cupV l Z h1 ∘ₗ pb l ι n).compr₂ (G.q h h2)) = (cupV l X h4).compl₂ (G.q h h3) :=
    LRingPf.ext2 fun x y => key x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hfg a) b

end UpperTheory.Gal.KunnethLefschetz
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem kunBij_holds : KunBij := by
  intro hIn l _ k _ _ hl hR d X p hp n
  obtain ⟨hprop, hsm⟩ := hp
  haveI := hprop
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  apply kun_bijective_of_kunIso l p p n (fun a m r h => hR.isCup _ a m r h)
  exact hIn.kun hIn.a2 hIn.a6nat hIn.a6ring hIn.a7 hIn.a8 hIn.a9 hIn.a10 hIn.a11 hIn.b1 hIn.b2
    hIn.b3 hIn.e2 hIn.e3 hIn.e4 l k (Ne.isUnit hl) p p n 0

end UpperTheory.Gal.KunnethLefschetz

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_self (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (n : ℤ) (x : V l X n) : pb l (𝟙 X) n x = x := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem pb_comp_apply (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.swap_holds :
    UpperTheory.Gal.KunnethLefschetz.Swap := by
  intro hP l _ k _ _ hl d X p hSP hR G n w h h' x
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  have hpair := (hP k d p inferInstance hsm).1
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hu := hR.mul_one X hunit
  have key : ∀ f : pullback p p ⟶ X, pullback.diagonal p ≫ f = 𝟙 X →
      cupV l (pullback p p) h (pb l f n x) (G.diag d p) = G.g hpair h x := by
    intro f hf
    have hd : G.diag d p = G.g hpair (show (0 : ℤ) + 2 * d = 2 * d by simp) (oneV l X) := by
      simp only [GysQ.diag, GysQ.cls, dif_pos hpair]
    rw [hd, ← G.proj hpair (show n + 0 = n by simp) h (show (0 : ℤ) + 2 * d = 2 * d by simp) h,
      ← pb_comp_apply, hf, pb_self, hu]
  rw [key _ (by simp), hR.comm (pullback p p) (2 * d) n w h' h,
    key _ (by simp), Int.negOnePow_even _ ⟨d * n, by ring⟩, one_smul]
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem slice_holds : Slice := by
  intro hP l _ k _ _ hl d X p hSP hR G y
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  obtain ⟨hdiag, hpt⟩ := hP k d p inferInstance hsm
  obtain ⟨hy, hpb⟩ := hpt y
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunit : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  simp only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]
  rw [G.nat hy hdiag (slice y) y.1
    (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]
  congr 1
  first
  | exact hR.one_nat y.1 hunitX
  | exact hR.one_nat y.1 hunit

end UpperTheory.Gal.KunnethLefschetz
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem rank_pos {K : Type} [Field K] {Z' : Scheme.{0}} (p' : Z' ⟶ TranscendenceTraces.gp K) [IsFinite p'] [Surjective p'] :
    1 ≤ p'.finrank (IsLocalRing.closedPoint K) := by
  have hF : Flat p' := inferInstance
  obtain ⟨x, hx⟩ := p'.surjective (IsLocalRing.closedPoint K)
  have h := p'.one_le_finrank_map x
  rwa [hx] at h

theorem injL_holds : InjL := by
  intro hT l _ X Y π hfin hsurj hint hloc hl n
  obtain ⟨hW, -, hD, hTr⟩ := hT
  haveI := hfin
  haveI := hsurj
  haveI := hint
  have hw : TranscendenceTraces.IsNwt π (TranscendenceTraces.nwt π) := hW π hloc
  let g : TranscendenceTraces.gp (Y.residueField (genericPoint Y)) ⟶ Y :=
    Y.fromSpecResidueField (genericPoint Y)
  have hpt : TranscendenceTraces.pt g = genericPoint Y :=
    Scheme.fromSpecResidueField_apply _ _
  have hpush := hD (Y.residueField (genericPoint Y)) (pullback.fst π g) (pullback.snd π g) π g
    (IsPullback.of_hasPullback π g) hloc hpt
  have hd := rank_pos (pullback.snd π g)
  have htr := hTr l n 0 π (TranscendenceTraces.nwt π) _ hw.1 hl hpush
  intro a b hab
  have key : ∀ c, ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) • c =
      TranscendenceTraces.trHQ l π (TranscendenceTraces.nwt π) n 0 (pb l π n c) := by
    intro c
    have := LinearMap.congr_fun htr c
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hne : ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) ≠ 0 := by
    norm_cast
    omega
  apply smul_right_injective _ hne
  simp only [key, hab]

end UpperTheory.Gal.KunnethLefschetz
end
end

section
namespace UpperTheory.Gal.KunnethLefschetz

theorem steps_holds : Steps :=
  ⟨offEx_holds, pairs_holds, pnFacts_holds, hypEmb_holds, finCov_holds, finFib_holds, comps_holds, ringL_holds, lowTL_holds, ptVanT_holds, lowL_holds, towerL_holds, affVan_holds, twBij_holds, gysTL_holds, gysinTwistZero_exists, qEasy_holds, limOnto_holds, qOnto_holds, qProj_holds, kunBij_holds, kunL_holds, swap_holds, slice_holds, ptInt_holds, detectL_holds, dualL_holds, finSupp_holds, pnCls_holds, injL_holds, trComp_holds, divL_holds, basisOne_holds, topPart_holds⟩

theorem qDual_holds (hI : In) (hT : TrIn) : QDual := steps_holds.qDual hI hT

theorem qDiag_holds (hI : In) (hT : TrIn) : QDiag := steps_holds.qDiag hI hT

end UpperTheory.Gal.KunnethLefschetz
end
