import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmoothStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixIntertwinesAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KerAppEqMapAppLEOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KSField

section Linear
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} {g : ℕ}

theorem isCob_const_mul (q : Y ⟶ Sp K) (a : K) {c : C1 U} (h : IsCob U c) :
    IsCob U (fun i j => constFn q (U i ⊓ U j) a * c i j) := by
  have := isCob_lc q (g := 1) (fun _ => a) (fun _ => c) fun _ => h
  convert this using 1
  funext i j
  simp [lc]

theorem matrix_comb (q : Y ⟶ Sp K) {φ θ θ' θ'' : Fin g → C1 U} (hφ : ∀ c, IsCob U (lc q c φ) → c = 0)
    {Θ Θ' Θ'' : Matrix (Fin g) (Fin g) K} (c : K) (h : ∀ b, IsCob U (θ b - lc q (Θ b) φ))
    (h' : ∀ b, IsCob U (θ' b - lc q (Θ' b) φ)) (h'' : ∀ b, IsCob U (θ'' b - lc q (Θ'' b) φ))
    (e : ∀ a, IsCob U (fun i j => θ'' a i j - constFn q _ c * θ a i j - θ' a i j)) : Θ'' = c • Θ + Θ' := by
  rw [← sub_eq_zero]
  funext b
  refine hφ _ ?_
  convert (((e b).sub (h'' b)).add (isCob_const_mul q c (h b))).add (h' b) using 1
  funext i j
  have : ∀ a, constFn q (U i ⊓ U j) ((Θ'' - (c • Θ + Θ')) b a) = constFn q (U i ⊓ U j) (Θ'' b a) -
      (constFn q (U i ⊓ U j) c * constFn q (U i ⊓ U j) (Θ b a) + constFn q (U i ⊓ U j) (Θ' b a)) := fun a => by
    simp [constFn]
  simp only [lc, Pi.add_apply, Pi.sub_apply, this, sub_mul, add_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
  ring

end Linear

def linearOfComb {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V → W)
    (h : ∀ (c : K) x y, f (c • x + y) = c • f x + f y) : V →ₗ[K] W where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

theorem lbIso_cube_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {s : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) {f f' : G ⟶ G} {f₀ f₀' : G' ⟶ G'}
    (hf : f₀.left ≫ φ = φ ≫ f.left) (hf' : f₀'.left ≫ φ = φ ≫ f'.left)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ f'] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ f₀, snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ f₀'] L') := by
  obtain ⟨w, hw⟩ := e
  have pa : ∀ {a : G ⟶ G} {a₀ : G' ⟶ G'}, a₀.left ≫ φ = φ ≫ a.left → ∀ {T : Over S'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ a₀) = pushPt h.1.w x ≫ a := fun ha _ x => Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have M : LBIso (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G' ≫ f₀, snd G' G'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card))
      (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G', snd G' G' ≫ f₀'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card)) := by
    refine LBIso.chartPull (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    · fin_cases i
      · exact (pa hf _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa hf' _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
    (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) M
      (iso_linComb ((isGen_iff w).1 hw) _ _).symm)

theorem isDerK_snd {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    IsDerK (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom (fun x => lam x.snd) := by
  refine ⟨fun a b => by simp, fun a b => ?_⟩
  simp [TrivSqZeroExt.snd_mul]

theorem spMap_fst_dirMap {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dirMap]

theorem exists_ksMatrix_of
    (href : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L')
    (hinv : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd)
    (hphi : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0)
    (hcoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a))
    (hlin : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j))
    (hsym : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ))
    (hend : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose)
    (hzero : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁)
    (htriv : Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j) :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  intro hL hL2 hC K _ _ r P P₀ φ₀ g v hp hI hv
  have hc : CompactSpace P.A.left := by
    have := P.isAb.proper
    exact QuasiCompact.compactSpace_of_compactSpace P.A.hom
  obtain ⟨L, hfin, hLB, haff, hiso⟩ := href _ P.L hc P.isLB
  have hI' : LBIso P₀.L (L.pull φ₀) := LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB hLB _) hI
    (hiso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  choose dd hdd using fun a => (hinv K P₀.A (v a) (hv.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := hphi K P₀ g v dd hv hdd _ φ₀ L hLB hI'
  have hind := (hφ' φ hφ).2
  choose d θ hks _ using fun lam : (Fin r → K) →ₗ[K] K =>
    hcoc K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 P.isAb.smooth _ L.ι L.U (isDerK_snd lam) haff
  choose Θ hΘ hΘ' using fun lam : (Fin r → K) →ₗ[K] K =>
    hsym hL hL2 hC K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ
  refine ⟨linearOfComb Θ fun c x y => matrix_comb P₀.A.hom hind c (hΘ' x) (hΘ' y) (hΘ' _)
    (hlin K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ c _ _ _ _ _ _ (hks x) (hks y)
      (hks (c • x + y))), hΘ, fun f f' f₀ f₀' F F' hf hf' e e' H hF hF' lam => ?_, fun lam h0 G _ ψ hψ => ?_⟩
  · exact hend K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ (Θ lam) f f₀ f₀' F F'
      (hΘ' lam) (PureType.isMonHom_over hp hp e) (PureType.isMonHom_over hp hp e') e
      (lbIso_cube_pull hp P.isLB P₀.isLB hI e e' H) hF hF'
  · have h0' : Θ lam = 0 := h0
    have hcob : ∀ a, IsCob _ (θ lam a) := fun a => by
      convert hΘ' lam a using 1
      funext i j
      simp [h0', lc, constFn]
    obtain ⟨d₁, hd₁⟩ := hzero K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ _ hLB.cover
      (hks lam) hcob
    have w : φ₀ ≫ P.A.hom = (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap (dirMap lam) := by
      rw [Category.assoc, spMap_fst_dirMap, hp.1.w]
    obtain ⟨j, hj, hj'⟩ : ∃ j : P₀.A.left ⟶ G.left, j ≫ ψ = φ₀ ∧
        j ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      ⟨hψ.1.lift _ _ w, hψ.1.lift_fst _ _ w, hψ.1.lift_snd _ _ w⟩
    have hD : (fun x : TrivSqZeroExt K (Fin r → K) => (dirMap lam x).snd) = fun x => lam x.snd :=
      funext fun x => TrivSqZeroExt.snd_map lam x
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, LocDerK P₀.A.hom P.A.hom (j ≫ ψ) (fun x => (dirMap lam x).snd) ⊤ d₂ := by
      rw [hj, hD]
      exact ⟨d₁, hd₁⟩
    obtain ⟨ρ, hρ, -, hρ'⟩ := htriv hL K P₀.A _ (dirMap lam) P.A G ψ j d₂ P₀.isAb
      (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hψ) hψ
      (hψ.cancel (hp.congr (spMap_fst_dirMap lam).symm hj.symm) hj') hd₂
    refine ⟨ρ, hρ, fun io h₁ h₂ => ?_⟩
    rw [hψ.1.hom_ext (h₁.trans hj.symm) (h₂.trans hj'.symm), hρ']

end GlobalTheory.KSField
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.FinAffineCharts

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem cocycle_on {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  rwa [map_mul, res_res, res_res, res_res] at this

noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩

theorem refineLB_isLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB where
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm)

theorem iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by
  refine ⟨⟨fun p => res (inf_le_inf_right _ (h p.1) : W p.1 ⊓ L.U p.2 ≤ L.U (c p.1) ⊓ L.U p.2)
    (L.g (c p.1) p.2)⟩, ?_⟩
  have key : ∀ (a b : κ) (i j : L.ι),
      res (inf_le_left : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ L.U i)
        (res (inf_le_inf_right _ (h a) : W a ⊓ L.U i ≤ L.U (c a) ⊓ L.U i) (L.g (c a) i)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ W b)
        (res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ L.U i ⊓ L.U j) (L.g i j))⁻¹ *
      res (inf_le_right : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W b ⊓ L.U j)
        (res (inf_le_inf_right _ (h b) : W b ⊓ L.U j ≤ L.U (c b) ⊓ L.U j) (L.g (c b) j)) := by
    intro a b i j
    rw [res_res, res_res, res_res, mul_right_comm, cocycle_on hL (c a) (c b) j _ _
      (le_inf (inf_le_left.trans (inf_le_left.trans (h a))) (inf_le_right.trans inf_le_right)),
      eq_mul_inv_iff_mul_eq]
    exact cocycle_on hL _ _ _ _ _ _
  exact fun p q => key p.1 q.1 p.2 q.2

theorem exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a,
    top_le_iff.1 ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem exists_finite_affine_charts : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L' := by
  intro X L _ hL
  obtain ⟨κ, hκ, W, c, hW, h, hc⟩ := exists_finite_affine_cover L hL
  exact ⟨refineLB L W c h, hκ, refineLB_isLB hL W c h hc, hW, iso_refineLB hL W c h⟩

end GlobalTheory.FinAffineCharts
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHomK {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHomK_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHomK p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_commK {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDerK_of_smooth : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  intro K _ R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHomK p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHomK_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHomK q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_commK x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHomK q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add])
    (fun a b => by rw [hD.2, hc, hc, map_add, map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := (GlobalTheory.T.existsUnique_localDerivationAlongFibreField_of_affine K R Y X q p m D W₀ hW).1 d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_derivation_lift_smooth_over_field : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  atlas_forward_decl GlobalTheory.KS.exists_locDerK_of_smooth
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Cocycle

theorem rsT_of_le {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = (Y.presheaf.map (homOfLE h).op).hom s := by
  unfold rsT; rw [dif_pos h]

theorem rsT_rsT {Y : Scheme.{0}} {O₀ O₁ O₂ : Y.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h', rsT_of_le h, rsT_of_le (h'.trans h), ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_add {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s + t) O = rsT s O + rsT t O := by
  simp only [rsT_of_le h, map_add]

theorem rsT_sub {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s t : Γ(Y, O₀)) :
    rsT (s - t) O = rsT s O - rsT t O := by
  simp only [rsT_of_le h, map_sub]

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dif_pos (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_zero' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) :
    constFn q O (0 : K) = 0 := by
  simp [constFn]

theorem locDerK_sub {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D : R → K} {W₁ W₂ W₀ : X.Opens} {d₁ d₂ : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h₁ : LocDerK q p m D W₁ d₁) (h₂ : LocDerK q p m D W₂ d₂) (l₁ : W₀ ≤ W₁) (l₂ : W₀ ≤ W₂) :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d₂ W f - d₁ W f) where
  add W hW f f' := by
    rw [h₁.add W (hW.trans l₁), h₂.add W (hW.trans l₂)]; ring
  mul W hW f f' := by
    rw [h₁.mul W (hW.trans l₁), h₂.mul W (hW.trans l₂)]; ring
  res W W' h hW f := by
    rw [h₁.res W W' h (hW.trans l₁), h₂.res W W' h (hW.trans l₂), rsT_sub (m.preimage_mono h)]
  base W hW r := by
    rw [h₁.base W (hW.trans l₁), h₂.base W (hW.trans l₂), sub_self, constFn_zero']

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem exists_ksCoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp hsp D I W hD hW
  choose d hder using fun i => GlobalTheory.T.exists_local_derivation_lift_smooth_over_field K R x₀ A₀.left X A₀.hom p m D (W i) hsp hp.w hD (hW i)
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose c hc using fun i j => (hb (W i ⊓ W j) _ (locDerK_sub (hder i) (hder j) inf_le_left inf_le_right)).exists
  have e : ∀ i j, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := fun i j => rfl
  have e3 : ∀ i j k, m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j ⊓ m ⁻¹ᵁ W k = m ⁻¹ᵁ (W i ⊓ W j ⊓ W k) := fun i j k => rfl
  refine ⟨d, fun a i j => rsT (c i j a) _, ⟨hder, ?_⟩, ?_⟩
  · intro i j O hO f
    rw [hc i j O hO f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rsT_rsT (e i j).le ((m.preimage_mono hO).trans (e i j).ge)]
  · intro a i j k
    have lij : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j := inf_le_left
    have ljk : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k := inf_le_inf_right _ inf_le_right
    have lik : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k := inf_le_inf_right _ inf_le_left
    have hu := (hb (W i ⊓ W j ⊓ W k) _
      (locDerK_sub (hder i) (hder k) (lik.trans inf_le_left) inf_le_right)).unique
      (y₁ := fun a => rsT (c i j a) _ + rsT (c j k a) _) (y₂ := fun a => rsT (c i k a) _)
      (by
        intro O hO f
        have h1 := hc i j O (hO.trans lij) f
        have h2 := hc j k O (hO.trans ljk) f
        have : d k O f - d i O f = (d j O f - d i O f) + (d k O f - d j O f) := by ring
        rw [this, h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_add (m.preimage_mono hO), rsT_rsT (m.preimage_mono lij) (m.preimage_mono hO),
          rsT_rsT (m.preimage_mono ljk) (m.preimage_mono hO), add_mul])
      (by
        intro O hO f
        rw [hc i k O (hO.trans lik) f]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [rsT_rsT (m.preimage_mono lik) (m.preimage_mono hO)])
    rw [rsT_rsT (e i j).le inf_le_left, rsT_rsT (e j k).le (inf_le_inf_right _ inf_le_right),
      rsT_rsT (e i k).le (inf_le_inf_right _ inf_le_left)]
    exact congrFun hu a

end GlobalTheory.KS.Cocycle
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.LinDir

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dif_pos (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_lin {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (c x y : K) :
    constFn q O (c * x + y) - constFn q O c * constFn q O x - constFn q O y = constFn q O 0 := by
  simp [constFn]

theorem locDerK_comb {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W hW, h'.add W hW, h''.add W hW]; ring
  mul W hW f f' := by
    rw [h.mul W hW, h'.mul W hW, h''.mul W hW]; ring
  res W W' l hW f := by
    rw [h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul,
      rsT_constFn q (m.preimage_mono l)]
  base W hW r := by
    rw [h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]

theorem locDerK_zero {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (W₀ : X.Opens) : LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) where
  add W hW f f' := by simp
  mul W hW f f' := by simp
  res W W' l hW f := by rw [rsT_zero]
  base W hW r := by simp [constFn]

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact GlobalTheory.T.invariantVectorFields_basis_verticalDerivations K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem ksCoc_linear : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp I W D D' c d d' d'' θ θ' θ'' h h' h'' a
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose b hbb using fun i => (hb (W i) _ (locDerK_comb (h.der i) (h'.der i) (h''.der i))).exists
  refine ⟨fun i => b i a, fun i j => ?_⟩
  have e : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := rfl
  have hu := (hb (W i ⊓ W j) _ (locDerK_zero A₀.hom p m _)).unique
    (y₁ := fun a => rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
      (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) _) (y₂ := fun _ => 0)
    (by
      intro O hO f
      have l : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j := (m.preimage_mono hO).trans e.ge
      have h1 := h.diff i j O hO f
      have h2 := h'.diff i j O hO f
      have h3 := h''.diff i j O hO f
      have h4 := hbb i O (hO.trans inf_le_left) f
      have h5 := hbb j O (hO.trans inf_le_right) f
      have : ∀ a, rsT (rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
          (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) (m ⁻¹ᵁ (W i ⊓ W j)))
          (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) =
          rsT (θ'' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - constFn A₀.hom (m ⁻¹ᵁ O) c * (rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f))
          - rsT (θ' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - (rsT (b j a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
            - rsT (b i a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) := by
        intro a
        rw [rsT_rsT e.ge (m.preimage_mono hO), rsT_sub, rsT_sub, rsT_sub, rsT_sub, rsT_mul,
          rsT_constFn _ l, rsT_rsT inf_le_left l, rsT_rsT inf_le_right l]
        ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← h1, ← h2, ← h3, ← h4, ← h5]
      ring)
    (by
      intro O hO f
      simp only [rsT_zero, zero_mul, Finset.sum_const_zero])
  have h0 := congrArg (fun s => rsT s (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j)) (congrFun hu a)
  simp only [] at h0
  rw [rsT_rsT e.ge e.le, rsT_self, rsT_zero] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.KS.LinDir
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.GlueDer

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem res_res {Y : Scheme.{0}} {U V V' : Y.Opens} (h : V ≤ U) (h' : V' ≤ V) (s : Γ(Y, U)) :
    resG Y h' (resG Y h s) = resG Y (h'.trans h) s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_app {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U) (f : Γ(X, U)) :
    resG Y h' ((m.app U).hom f) = (m.app V).hom (resG X h f) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, m.naturality]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn p U a) = constFn p V a := by
  simp only [resG, constFn]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem app_const {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by
  have h1 : (m.app U).hom (constFn p U a) = constFn (m ≫ p) (m ⁻¹ᵁ U) a := by
    simp only [constFn]
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE m p ⊤ U (m ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl)
  rw [h1, hm]
  simp only [constFn]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x₀ a) =
      ((spMap x₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x₀)
    exact congrArg (fun φ => φ.hom a) this
  rw [h2]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.comp_appLE q (spMap x₀) ⊤ (m ⁻¹ᵁ U) (fun _ _ => trivial))

theorem pre_mono {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hx => h hx

theorem pre_cover {Y X : Scheme.{0}} (m : Y ⟶ X) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤) (O : X.Opens) :
    m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := by
  intro y hy
  have : m y ∈ ⨆ i, W i := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩

theorem glue {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) : ∃ d₁, LocDerK q p m D ⊤ d₁ := by
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ?_, ?_, ?_, ?_⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, hd, hd, hd, map_add, (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]

end GlobalTheory.KS.GlueDer

open GlobalTheory.KS.GlueDer in

theorem GlobalTheory.KS.exists_global_locDer_of_isCob : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁ := by
  intro K _ A₀ _ g v dd _ hv hdd R _ x₀ X p m hm I W D d θ hW hc hb
  choose b hb using hb
  have H := fun a => (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hv.1 a)).2 (dd a) (hdd a)
  refine glue A₀.hom p m D W hW
    (fun i O f => d i O f - ∑ a, rsT (b a i) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) (fun i => ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro O hO f f'
      simp only [(hc.der i).add O hO, map_add, fun a => (H a).1, mul_add, Finset.sum_add_distrib]
      ring
    · intro O hO f f'
      simp only [(hc.der i).mul O hO, map_mul, fun a => (H a).2.1, mul_add, Finset.sum_add_distrib, mul_sub,
        Finset.mul_sum, mul_left_comm (rsT _ _)]
      ring
    · intro O O' h hO f
      have h' := pre_mono m h
      rw [(hc.der i).res O O' h hO, rsT_eq h', rsT_eq h', map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 := (H a).2.2.1 _ _ ((m.app O).hom f) h'
      rw [rsT_eq h', rsT_eq h', res_app m h] at h2
      rw [map_mul, h2, rsT_eq (pre_mono m hO), rsT_eq (pre_mono m (h.trans hO)), res_res]
    · intro O hO r
      simp only [(hc.der i).base O hO, app_const x₀ p A₀.hom m hm.w, fun a => (H a).2.2.2.1, mul_zero,
        Finset.sum_const_zero, sub_zero]
  · intro i j O hO f
    have h1 := hc.diff i j O hO f
    have hi : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i := pre_mono m (hO.trans inf_le_left)
    have hj : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W j := pre_mono m (hO.trans inf_le_right)
    have h2 : ∀ a, rsT (θ a i j) (m ⁻¹ᵁ O) = rsT (b a j) (m ⁻¹ᵁ O) - rsT (b a i) (m ⁻¹ᵁ O) := by
      intro a
      rw [hb, rsT_eq (le_inf hi hj), map_sub, rsT_eq inf_le_right, rsT_eq inf_le_left, res_res, res_res,
        rsT_eq hi, rsT_eq hj]
    simp only [h2, sub_mul, Finset.sum_sub_distrib] at h1
    show _ - _ = _ - _
    linear_combination -h1
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsIso

theorem ker_fst_eq_span (K : Type) [Field K] :
    RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h0 : x.fst = 0 := hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext
    · simp [h0]
    · simp
  · rintro ⟨y, rfl⟩
    show (DualNumber.eps * y).fst = 0
    simp

set_option maxHeartbeats 1000000 in
private theorem exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    ∃ d : C, c = a DualNumber.eps * d := by
  let _ : Algebra (DualNumber K) C := a.toAlgebra
  have _ : Module.Flat (DualNumber K) C := ha
  have hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hc
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C)
    (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum
  have hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd := by
    intro i
    have h1 : DualNumber.eps * b () i = 0 := by
      have h0 := hb i
      rwa [Fintype.sum_unique] at h0
    have h2 : (b () i).fst = 0 := by
      have h3 := congrArg TrivSqZeroExt.snd h1
      rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add,
        TrivSqZeroExt.snd_zero] at h3
      exact h3
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]
    · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul,
        TrivSqZeroExt.fst_inl]
  refine ⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩
  rw [show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hki := hkill i
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  conv_lhs => rw [hki]
  rw [map_mul, _root_.mul_assoc]

theorem mem_span_of_flat {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    c ∈ Ideal.span {a DualNumber.eps} := by
  rw [Ideal.mem_span_singleton]
  exact exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc

theorem bijective_of_mod_eps {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by
  have hee : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hk : jC (φ (a DualNumber.eps)) = 0 := by
    rw [← RingHom.mem_ker, hC]
    exact Ideal.mem_span_singleton_self _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : b ∈ RingHom.ker jB := by rw [RingHom.mem_ker, ← hφ, hb, map_zero]
    rw [hB, Ideal.mem_span_singleton] at h1
    obtain ⟨b1, rfl⟩ := h1
    have h2 : (φ.comp a) DualNumber.eps * φ b1 = 0 := by
      rw [RingHom.comp_apply, ← map_mul]
      exact hb
    have h3 := mem_span_of_flat (φ.comp a) hfl (φ b1) h2
    rw [Ideal.mem_span_singleton] at h3
    obtain ⟨c', hc'⟩ := h3
    have h4 : b1 ∈ RingHom.ker jB := by
      rw [RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]
    rw [hB, Ideal.mem_span_singleton] at h4
    obtain ⟨b2, rfl⟩ := h4
    rw [← _root_.mul_assoc, hee, zero_mul]
  · intro c
    obtain ⟨b, hb⟩ := hs (jC c)
    have h1 : c - φ b ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨b1, hb1⟩ := hs (jC c1)
    have h2 : c1 - φ b1 ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h2
    obtain ⟨c2, hc2⟩ := h2
    have hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0 := by
      rw [← map_mul, hee, map_zero]
    refine ⟨b + a DualNumber.eps * b1, ?_⟩
    rw [map_add, map_mul]
    linear_combination (-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe

theorem fst_surjective (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := by
  intro x
  exact ⟨algebraMap K (DualNumber K) x, by simp⟩

theorem isHomeomorph_of_isPullback {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by
  have hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) := rfl
  have hsurj := fst_surjective K
  have hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [hsp]
    exact IsClosedImmersion.spec_of_surjective _ hsurj
  have hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ := by
      rw [range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom)
        (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      rw [SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      show _ ∈ nilradical _
      rw [mem_nilradical]
      exact ⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩
    rw [hsp]
    exact ⟨fun p => Set.range_eq_univ.1 hr p⟩
  have hcj : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci
  have hsj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu
  refine ⟨hcj, ?_⟩
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩

theorem isAffineHom_of_isHomeomorph {X Y : Scheme.{0}} (e : X ⟶ Y) (he : IsHomeomorph e) :
    IsAffineHom e := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := he.surjective y
  have hmem : e x ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ e ⁻¹ᵁ V from hxV)
  let O : Y.Opens := ⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩
  obtain ⟨g, hgO, hgy⟩ := (show IsAffineOpen V from hV).exists_basicOpen_le (V := O)
    ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV
  have hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgO hz
    rwa [← he.injective hwz]
  refine ⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩
  have heq : e ⁻¹ᵁ Y.basicOpen g =
      X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 hsub).symm
  rw [heq]
  exact (show IsAffineOpen W from hW).basicOpen _

end GlobalTheory.EpsIso

namespace GlobalTheory

theorem isIso_of_id_mod_eps : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  intro K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj
  subst hπ hj
  obtain ⟨hcj, hhj⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h
  obtain ⟨hcj', hhj'⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'
  have hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j := rfl
  have hhe : IsHomeomorph e := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨e.continuous, ?_, ?_⟩
    · intro F hF
      have hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F) := by
        rw [hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]
      rw [hF']
      exact hhj'.isClosedMap _ (hF.preimage j.continuous)
    · have hb := hhj'.bijective
      rw [hcf] at hb
      exact (Function.Bijective.of_comp_iff _ hhj.bijective).1 hb
  have hA : IsAffineHom e := GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe
  have hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    GlobalTheory.EpsIso.fst_surjective K
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := GlobalTheory.EpsIso.ker_fst_eq_span K
  have hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W) := by
    intro W hW
    have hW' : IsAffineOpen (e ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE ..).symm
    have hB := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW
    have hC := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'
    rw [hker, Ideal.map_span, Set.image_singleton] at hB hC
    have hC' := hC.trans (congrArg
      (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)
    have hfl' := HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top
    have hfl2 := (congrArg (fun g => g.hom.Flat) hcomp).mp hfl'
    have hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    have hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
        π'.appLE ⊤ W le_top).hom).Flat := by
      have heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
          π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom := by
        exact RingHom.ext fun x => rfl
      rw [heq]
      exact RingHom.Flat.comp hg hfl2
    have := hcj'
    have hbij := GlobalTheory.EpsIso.bijective_of_mod_eps
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom
      (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl)
      (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0})
    (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_
  have hsrc : IsAffine (e ⁻¹ᵁ V.1) := IsAffineHom.isAffine_preimage _ V.2
  have htgt : IsAffine V.1 := V.2
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]
  have hV : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)
  have hb2 : Function.Bijective
      (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact isIso_SpecMap_iff.2 (hb2.comp hb1)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_id_mod_eps_thickening : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  atlas_forward_decl GlobalTheory.isIso_of_id_mod_eps
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_isPullback :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ρ₀ : A'.left ⟶ A₀.left) (j : A₀.left ⟶ A'.left), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → IsPullback ρ₀ A'.hom A₀.hom (spMap (algebraMap K (DualNumber K))) → j ≫ ρ₀ = 𝟙 _ → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro L K _ A₀ _ A' _ ρ₀ j h₀ h' hj hρ hjρ
  obtain ⟨ρ, h₁, h₂⟩ := exists_isGrpPullback_retraction L.rigidity A₀ A' _ _ ρ₀ j h₀ h' hj hρ hjρ
  exact ⟨ρ, h₁, hj, h₂⟩

end GlobalTheory.KS
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_locDerK :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro hL K _ A₀ _ R _ xD A _ A' _ ψ j d hA₀ hA' hψ hj hd

  have hra : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of K)
    ext x
    simp
  have : Flat A₀.hom := inferInstance

  have hρ : IsPullback (pullback.fst A₀.hom (spMap (algebraMap K (DualNumber K)))) (pullback.snd _ _)
      A₀.hom (spMap (algebraMap K (DualNumber K))) := IsPullback.of_hasPullback _ _
  obtain ⟨j₀, hj₀ρ, hj₀π⟩ : ∃ j₀ : A₀.left ⟶ pullback A₀.hom (spMap (algebraMap K (DualNumber K))),
      j₀ ≫ pullback.fst _ _ = 𝟙 _ ∧
        j₀ ≫ pullback.snd _ _ = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
    ⟨pullback.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
      (by rw [Category.assoc, hra, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hj₀ : IsPullback j₀ A₀.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K))))
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hj₀π hρ
    rw [hj₀ρ, hra]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

  have hm : (j ≫ ψ) ≫ A.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hΦj, hΦp, -⟩ := DerMorK.exists_hom_of_derivation K A₀.left _ A₀.hom (pullback.snd _ _)
    (pullback.fst _ _) j₀ hρ hj₀ρ hj₀π R xD A.left A.hom (j ≫ ψ) d hm hd

  obtain ⟨e, heψ, heh⟩ : ∃ e : pullback A₀.hom (spMap (algebraMap K (DualNumber K))) ⟶ A'.left,
      e ≫ ψ = Φ ∧ e ≫ A'.hom = pullback.snd _ _ :=
    ⟨hψ.1.lift Φ _ hΦp, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have hje : j₀ ≫ e = j := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, heψ, hΦj]
    · rw [Category.assoc, heh, hj₀π, hj.1.w]

  have : IsIso e := GlobalTheory.T.isIso_of_id_mod_eps_thickening K A₀.left _ A'.left A₀.hom (pullback.snd _ _) A'.hom j₀ j e hj₀ hj.1
    inferInstance heh hje
  refine exists_isConstK_of_isPullback hL K A₀ A' (inv e ≫ pullback.fst _ _) j hA₀ hA' hj ?_ ?_
  · have h1 : IsPullback (inv e) A'.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heh]⟩
    have h2 := h1.paste_horiz hρ
    rwa [Category.id_comp] at h2
  · rw [← hje, Category.assoc, IsIso.hom_inv_id_assoc, hj₀ρ]

end GlobalTheory.KS
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.KSField.exists_ksMatrix : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ :=
  GlobalTheory.KSField.exists_ksMatrix_of GlobalTheory.FinAffineCharts.exists_finite_affine_charts GlobalTheory.KS.InvField.main GlobalTheory.KS.DlogPol.dlog_independent GlobalTheory.KS.Cocycle.exists_ksCoc GlobalTheory.KS.LinDir.ksCoc_linear GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.KS.matrix_intertwines_adjoint GlobalTheory.KS.exists_global_locDer_of_isCob GlobalTheory.KS.exists_isConstK_of_locDerK
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ksMatrix_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  atlas_forward_decl GlobalTheory.KSField.exists_ksMatrix
end
