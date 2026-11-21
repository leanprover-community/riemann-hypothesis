import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSgl : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      lam.mul U 0 t t (zero_add t) (Sec.map (sglι (tw q 0)) a) b = L U t a b

def LeafExtAlongAug : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (lam : Pair (sgl (tw q 0)) (res _ (tw q i)) (res _ (tw q i))),
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (x : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b = lam.mul U 0 t t (zero_add t) x b

section Act
variable {q : ℕ} {i : ℤ}

def actPair (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) : Sec ((sgl (tw q 0)).X s) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)]
      Sec ((res _ (tw q i)).X w) U :=
  if hs : s = 0 then
    ((L U t).compl₁₂ (((HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) s hs).hom.hom.app (op U)).hom)
      LinearMap.id).compr₂ ((((res _ (tw q i)).XIsoOfEq (show t = w by omega)).hom.hom.app (op U)).hom)
  else 0

theorem actPair_pos (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (t : ℤ)
    (a : Sec ((sgl (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U) :
    actPair L U 0 t t (zero_add t) a b =
      L U t (Sec.map (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (tw q 0) 0 rfl).hom a) b := by
  simp [actPair, HomologicalComplex.XIsoOfEq_rfl]
  rfl

theorem actPair_neg (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (hs : s ≠ 0) : actPair L U s t w h = 0 := by
  simp [actPair, hs]

end Act

theorem LeafPairExt_of (h1 : LeafActSgl) (h2 : LeafExtAlongAug) : LeafPairExt := by
  intro q _ i L hL
  obtain ⟨lam, hlam⟩ := h1 q i L hL
  obtain ⟨ν, hν⟩ := h2 q i lam
  refine ⟨ν, fun U t a b => ?_⟩
  have e : Sec.map (resι _ (tw q 0)) a = Sec.map ((resAug (tw q 0)).f 0) (Sec.map (sglι (tw q 0)) a) := rfl
  rw [e, hν, hlam]

theorem etale_twist_action_induces_single_complex_pairing_holds : LeafActSgl := by
  intro q _ i L hL
  refine ⟨⟨actPair L, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, hL.1]
      congr 2
    · rw [actPair_neg L U s t w h hs, actPair_neg L V s t w h hs]
      simp
  · intro U s t w h a b
    have hd : (sgl (tw q 0)).d s (s + 1) = 0 := by simp
    rw [hd]
    have h0 : Sec.map (0 : (sgl (tw q 0)).X s ⟶ (sgl (tw q 0)).X (s + 1)) a = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply, zero_add]
    by_cases hs : s = 0
    · subst hs
      obtain rfl : w = t := by omega
      rw [actPair_pos, actPair_pos, Int.negOnePow_zero, one_smul]
      exact hL.2 U _ _ b
    · rw [actPair_neg L U s t w h hs, actPair_neg L U s (t + 1) (w + 1) (by omega) hs]
      simp
  · intro U t a b
    change actPair L U 0 t t (zero_add t) _ b = _
    rw [actPair_pos]
    congr 1

theorem LeafPairExt_of' (h2 : LeafExtAlongAug) : LeafPairExt := LeafPairExt_of etale_twist_action_induces_single_complex_pairing_holds h2

end LateralTheory.E.LeafPairExtPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
end
end
