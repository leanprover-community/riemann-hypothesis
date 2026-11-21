import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsProjOverSPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PFnDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHopWord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGeoStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTransPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr

section
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.HodgeCoh

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem trace_comb {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ} {A : Type*}
    (u : Fin m → Module.End ℂ M) (c : Fin m → ℂ) (w : A →₀ ℂ) (e : A → Module.End ℂ M) :
    LinearMap.trace ℂ M ((∑ i, c i • u i) ∘ₗ w.sum fun α r => r • e α) =
      ∑ i, c i * w.sum fun α r => r * LinearMap.trace ℂ M (u i ∘ₗ e α) := by
  simp only [Finsupp.sum, ← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
  ring

private theorem sum_rearrange {m : ℕ} {A : Type*} (R : Finset ℕ) (S : Finset A) (c : Fin m → ℂ) (w : A → ℂ)
    (x z : ℕ → ℂ) (t : Fin m → A → ℕ → ℕ → ℂ) :
    ∑ a ∈ R, x a * ∑ b ∈ R, z b * ∑ i, c i * ∑ α ∈ S, w α * t i α a b =
      ∑ i, c i * ∑ α ∈ S, w α * ∑ a ∈ R, x a * ∑ b ∈ R, z b * t i α a b := by
  simp only [Finset.mul_sum]
  calc _ = ∑ a ∈ R, ∑ i, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) := Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ α ∈ S, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ α ∈ S, ∑ a ∈ R, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

private theorem alt_family {M : ℕ → ℕ → Type*} [∀ a b, AddCommGroup (M a b)] [∀ a b, Module ℂ (M a b)]
    (d m : ℕ) {A : Type*} (u : Fin m → ∀ a b : ℕ, Module.End ℂ (M a b)) (c : Fin m → ℂ) (w : A →₀ ℂ)
    (e : A → ∀ a b : ℕ, Module.End ℂ (M a b)) (y : ℂ) :
    ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
        LinearMap.trace ℂ (M a b) ((∑ i, c i • u i a b) ∘ₗ w.sum fun α r => r • e α a b) =
      ∑ i, c i * w.sum fun α r => r * ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b) := by
  simp only [trace_comb]
  simp only [Finsupp.sum]
  exact sum_rearrange (Finset.range (d + 1)) w.support c (fun α => w α) (fun a => (-y) ^ a) (fun b => (-1 : ℂ) ^ b)
    fun i α a b => LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b)

theorem altLin_of : AltLin := fun Z s d m A u c w e y =>
  alt_family (M := fun a b => hodgeH s a b) d m u c w e y

end UpperTheory.Gal.LocalSmoothExtension
end
end

section
open UpperTheory.Gal.LocalSmoothExtension

set_option maxHeartbeats 1000000 in
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.HodgeCoh in
theorem UpperTheory.Gal.LocalSmoothExtension.occOf_of :
    MemOp → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.BcGood.{0} → UpperTheory.Gal.G3.OpBc.{0} → UpperTheory.Gal.G3.OpTr.{0} → UpperTheory.Gal.G3.BcSplits → OccOf := by
  intro memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe
  letI : Algebra R ℂ := τ.toAlgebra
  refine ⟨b, x, hx, fun j => ?_⟩
  obtain ⟨-, hfin, het, hop⟩ := memop p D G L R gb k T N J g j
  haveI := hfin
  haveI := het
  have hΘ := bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)
  have hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q := rfl
  have h2 := opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs
    ((T.tower N g).comm j) _ (hop _ hΘ)
  obtain ⟨hf', he', -⟩ := bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs
    ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)
  haveI := hf'
  haveI := he'
  have ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) := by
    unfold UpperTheory.Gal.G3.bcMap
    rw [pullback.lift_snd, pullback.lift_snd]
  have htr' := htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _
    (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl
  have hA := (optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2
  have e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs := rfl
  refine ⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩
  rw [hA]
  rfl
end

section
open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Gal.Int.Geo in
theorem UpperTheory.Gal.LocalSmoothExtension.kSHodge_of :
    HodgeEig → KSBc → SpecConj → MemOp → FnDecomp → OccOf → UpperTheory.Gal.Int.Geo.KSHodge := by
  intro hE hB hS hM hF hO p _ D G L sc lam anti
  obtain ⟨k, hk⟩ := hE p D G L sc lam anti
  refine ⟨k, ?_⟩
  intro R _ _ gb T N J g θ f hf hs τ hρ ht σ i₀ h hh i
  let gb' : GBase D.toG ℂ :=
    { ρ := D.ρc
      ρ_root := D.toG.ρc_root
      t := fun i => (D.toG.tau i).comp (algebraMap _ _)
      t_ω := fun i => D.toG.tau_ω i
      comax := fun i j hij => by
        have ha : D.toG.a = 1 := sc.a1
        exact absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij }
  have hstd : StdC D gb' := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨⟨X', lev', c1, c2, c3, c4, c5, c6⟩, hX, hl⟩ :=
    hB p D G L R gb k T τ gb' hρ.symm (fun i c => (ht i c).symm)
  dsimp only at hX
  subst hX
  cases hl
  have e : (fun (j : J) (y : G.GAf) => σ ((g j).fn y)) = fun j => (g j).fn := by
    funext j y
    exact map_natCast σ _
  have h1 := hS σ p D G L lam (L.KN N.1) J (fun j => (g j).fn) θ f hs
  rw [e] at h1
  have hfn : T.X.IsFn (T.lev N) f := by
    refine (hF _ _ T.X (T.lev N) f).2 ?_ ?_
    · rw [T.K_eq]; exact hf.1
    · intro y hy
      exact (T.Δ_eq _).2 (hf.2 y hy)
  have hfn' : T.X.IsFn (T.lev N) fun y => σ (f y) := by
    obtain ⟨a1, a2, a3⟩ := hfn
    refine ⟨fun k hk y => ⟨?_, ?_⟩, fun y hy => a2 y ?_, a3.subset fun y hy => ?_⟩
    · show σ _ = σ _
      rw [(a1 k hk y).1]
    · show σ _ = σ _
      rw [(a1 k hk y).2]
    · exact fun h0 => hy (by show σ (f y) = 0; rw [h0, map_zero])
    · exact fun h0 => hy (by show σ (f y.out) = 0; rw [h0, map_zero])
  obtain ⟨b, x, hx, hx'⟩ := hk gb' hstd ⟨_, T.lev, c1, c2, c3, c4, c5, c6⟩ N σ i₀ h hh J (fun j => (g j).fn)
    (fun j => σ (θ j)) (fun y => σ (f y)) (fun j => (hM p D G L R gb k T N J g j).1) hfn' h1 i
  exact hO p D G L R gb k T N J g τ _ (h i) b x hx hx'
end

section
open UpperTheory.Gal.LocalSmoothExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory.UPel.HT.MapComp

theorem UpperTheory.Gal.LocalSmoothExtension.mapEq_of :
    MapEq := by
  intro G R _ _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₂
  refine ⟨fun m₁ => ?_, fun m => ?_⟩
  · refine ⟨⟨m₁.φ ≫ m₂.φ, m₁.φ₂ ≫ m₂.φ₂, IsGrpPullback.comp m₁.cart m₂.cart,
      isSquare_comp m₁.sq m₂.sq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
        (lbIso_pull_comp m₂.pol m₁.φ₂ rfl), fun y => ?_⟩, rfl⟩
    · rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
    · rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]
  · have hw : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by
      rw [Category.assoc]; exact m.cart.1.w
    let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) hw
    have h₁ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
    obtain ⟨φ₂, hsq⟩ := exists_isSquare h₂
    have h₃ : φ₂ ≫ m₂.φ₂ = m.φ₂ := by
      have := isSquare_comp hsq m₂.sq
      rw [h₁] at this
      exact isSquare_unique this m.sq
    have hc : IsGrpPullback o₁.A o₂.A f φ :=
      IsGrpPullback.cancel m₂.cart (by rw [h₁]; exact m.cart) h₂
    refine ⟨⟨φ, φ₂, hc, hsq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
        (lbIso_pull_comp m₂.pol φ₂ h₃.symm).symm, fun y => ?_⟩, h₁⟩
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.act, Category.assoc, m₂.act, ← Category.assoc, h₁]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.eta, Category.assoc, Category.assoc, m₂.eta]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
        simp

end
end

section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.Gen.BaseChange

theorem UpperTheory.Gal.LocalSmoothExtension.modelBc_of :
    MapEq → ModelBc := by
  intro hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M
  obtain ⟨o', ⟨mo⟩⟩ := exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ
  let U : GObj gb₂ N (pullback.snd M.s (spMap τ)) := up hρ ht pullback.condition.symm o'
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'),
      ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j) := by
    intro S s' o
    let u : GObj gb₁ N (s' ≫ spMap τ) := down hρ ht rfl o
    obtain ⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩ := M.rep S _ u
    let j : S ⟶ pullback M.s (spMap τ) := pullback.lift a s' ha
    have j₁ : j ≫ pullback.fst M.s (spMap τ) = a := pullback.lift_fst _ _ _
    have j₂ : j ≫ pullback.snd M.s (spMap τ) = s' := pullback.lift_snd _ _ _
    obtain ⟨mj, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)
    have mj' : GObjMap o U j := ⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩
    refine ⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩
    rintro j' ⟨h₂, ⟨m'⟩⟩
    have m'' : GObjMap u o' j' := ⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩
    obtain ⟨n, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''
    have e : j' ≫ pullback.fst M.s (spMap τ) = a :=
      hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩
    apply pullback.hom_ext
    · rw [e, j₁]
    · rw [h₂, j₂]
  refine ⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ),
    IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩
end

section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem UpperTheory.Gal.LocalSmoothExtension.homEx_of :
    HomEx := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  have ext'' : ∀ {T : Over S₁} (u v : T ⟶ o₁''.A), u.left ≫ m''.φ = v.left ≫ m''.φ → u = v := by
    intro T u v h
    apply Over.OverMorphism.ext
    exact m''.cart.1.hom_ext h (by rw [Over.w u, Over.w v])
  have p' : ∀ (T : Over S₁) (x : T ⟶ o₁'.A), (pushHom m'.cart T x).left = x.left ≫ m'.φ :=
    fun _ _ => rfl
  have p'' : ∀ (T : Over S₁) (x : T ⟶ o₁''.A), (pushHom m''.cart T x).left = x.left ≫ m''.φ :=
    fun _ _ => rfl
  refine ⟨?_, fun ψ₁ ψ₂ h => ext'' ψ₁ ψ₂ h, ?_⟩
  · intro ψ hψ
    haveI := hψ
    have w : (m'.φ ≫ ψ.left) ≫ o''.A.hom = o₁'.A.hom ≫ f := by
      rw [Category.assoc, Over.w ψ, m'.cart.1.w]
    let ψ₁ : o₁'.A ⟶ o₁''.A :=
      Over.homMk (m''.cart.1.lift (m'.φ ≫ ψ.left) o₁'.A.hom w) (m''.cart.1.lift_snd _ _ w)
    have hψ₁ : ψ₁.left ≫ m''.φ = m'.φ ≫ ψ.left := m''.cart.1.lift_fst _ _ w
    refine ⟨ψ₁, ?_, hψ₁⟩
    apply isMonHom_of_mul
    intro T x y
    apply ext''
    have e : ∀ z : T ⟶ o₁'.A, pushHom m''.cart T (z ≫ ψ₁) = pushHom m'.cart T z ≫ ψ := by
      intro z
      apply Over.OverMorphism.ext
      rw [p'', Over.comp_left, Over.comp_left, p', Category.assoc, Category.assoc, hψ₁]
    rw [← p'', ← p'', map_mul, e, e, e, map_mul, mul_comp]
  · intro d
    let e : Over.mk (o₁'.A.hom ≫ f) ⟶ o'.A := pushHom m'.cart o₁'.A (𝟙 o₁'.A)
    have h1 : (𝟙 o₁'.A ^ d).left ≫ m'.φ = (e ^ d).left := by
      rw [← p', map_pow]
    have h2 : m'.φ ≫ (𝟙 o'.A ^ d).left = (e ^ d).left := by
      have : e ≫ 𝟙 o'.A ^ d = e ^ d := by rw [comp_pow, Category.comp_id]
      rw [← this, Over.comp_left, p', Over.id_left, Category.id_comp]
    rw [h1, h2]
end

section
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private theorem isSquare_square_compatible_homs {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A']
    [IsCommMonObj A'] (ψ : A ⟶ A') : Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.LocalSmoothExtension.polPull_of :
    PolPull := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hc c ⟨h⟩
  letI := o'.grp
  letI := o'.comm
  letI := o''.grp
  letI := o''.comm
  letI := o₁'.grp
  letI := o₁'.comm
  letI := o₁''.grp
  letI := o₁''.comm
  have hsq : Hecke.sq2 ψ₁ ≫ m''.φ₂ = m'.φ₂ ≫ Hecke.sq2 ψ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp (isSquare_square_compatible_homs ψ₁) m''.sq)
    rw [hc]
    exact MapComp.isSquare_comp m'.sq (isSquare_square_compatible_homs ψ)
  have hp : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
  have hp₁ : (Hecke.lbPow o₁'.P c).IsLB := LB.isLB_linComb o₁'.isLB _ _
  have hq : (o''.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o''.isLB _
  have hA := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
  have hB := (GlobalTheory.CechPic.cls_eq_iff o₁''.isLB (pull_isLB o''.isLB m''.φ₂)).2 m''.pol
  have hC := (GlobalTheory.CechPic.cls_eq_iff hp hq).2 h
  refine ⟨(GlobalTheory.CechPic.cls_eq_iff hp₁ (pull_isLB o₁''.isLB _)).1 ?_⟩
  rw [GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB, hA, GlobalTheory.CechPic.cls_pull o'.isLB,
    GlobalTheory.CechPic.cls_pull o₁''.isLB, hB, GlobalTheory.CechPic.cls_pull o''.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
    GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o''.isLB (Hecke.sq2 ψ) hq, ← hC,
    GlobalTheory.BirigidPow.cls_lbPow o'.isLB, map_nsmul]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.tatePull_of :
    TatePull := by
  intro p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I
  letI := o.grp
  letI := o₁.grp
  letI := o.comm
  have hl : ∀ x : Over.mk t ⟶ o₁.A,
      Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ := fun _ => rfl
  let E := MulEquiv.ofBijective (pushHom m.cart (Over.mk t))
    ⟨push_injective m.cart _, push_surjective m.cart _⟩
  have key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q := fun q => by
    rw [← hl]
    exact congrArg Over.Hom.left (E.apply_symm_apply q)
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n y => E.symm (I.ev n y),
            add := fun n x y => by simp only [I.add, map_mul],
            lin := fun n c x => ?_,
            ker := fun n hn x => by
              rw [← I.ker n hn x]
              exact E.symm.map_eq_one_iff,
            onto := fun n hn q => ?_,
            tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],
            isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩
  · have h1 := push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))
    have h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x := E.apply_symm_apply _
    rw [h2] at h1
    apply E.injective
    rw [E.apply_symm_apply, I.lin]
    exact h1.symm
  · constructor
    · intro hq
      obtain ⟨x, hx⟩ := (I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])
      exact ⟨x, by rw [hx, E.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]
  · exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _)
      m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2
      (I.isom n hn x y)
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down exists_gObjMap_pull spMap_comp')
open UpperTheory.Gal.Int.Geo (IsTrans)
open UpperTheory.Gal.LocalSmoothExtension

private theorem objMap_along {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj b N s'} {o : GObj b N s} {f g : S' ⟶ S}
    (e : f = g) (n : GObjMap o' o f) : ∃ n' : GObjMap o' o g, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

theorem UpperTheory.Gal.LocalSmoothExtension.legBc_of :
    MapEq → TransPull → LegBc := by
  intro hME hTP p _ D G L R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N N' M M' P P' f f' hf hf' m m' h π o ψ φ hπ hψ
  have hw : (f' ≫ π) ≫ M.s = P'.s ≫ spMap τ := by
    rw [Category.assoc, hπ]
    exact hf'.w
  obtain ⟨π₁, hπf, hπs⟩ : ∃ π₁ : P'.X ⟶ P.X, π₁ ≫ f = f' ≫ π ∧ π₁ ≫ P.s = P'.s :=
    ⟨hf.lift (f' ≫ π) P'.s hw, hf.lift_fst _ _ _, hf.lift_snd _ _ _⟩
  obtain ⟨o₁, ⟨φ₁⟩⟩ : ∃ o₁ : GObj gb₂ N P'.s, Nonempty (GObjMap o₁ P.univ π₁) := by
    have key := exists_gObjMap_pull π₁ P.univ
    rw [hπs] at key
    exact key
  let d₁ : GObj gb₁ N (P'.s ≫ spMap τ) := down hρ ht rfl o₁
  let φd : GObjMap d₁ (down hρ ht rfl P.univ) π₁ :=
    ⟨φ₁.φ, φ₁.φ₂, φ₁.cart, φ₁.sq, φ₁.act, φ₁.pol, φ₁.eta⟩
  obtain ⟨n, hn⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ (down hρ ht rfl P.univ) M.univ π₁ f m).1 φd
  obtain ⟨n', hn'⟩ := objMap_along hπf n
  obtain ⟨m'', hm''⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ o M.univ f' π φ).2 n'
  obtain ⟨ψ₁, hψ₁, hT⟩ := hTP p D G L R₁ gb₁ N N' _ _ M'.s (P'.s ≫ spMap τ) f' hf'.w M'.univ o
    (down hρ ht rfl P'.univ) d₁ m' m'' h ψ hψ
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := hT
  refine ⟨π₁, o₁, ψ₁, φ₁, hπs, ⟨t₁, t₂, t₃, t₄, fun k _ _ t β hβ => ?_⟩, hπf, ?_⟩
  · exact t₅ k t (β.comp τ) (by rw [spMap_comp', ← Category.assoc, hβ])
  · have e : φ₁.φ ≫ m.φ = m''.φ ≫ φ.φ := by
      rw [hm'', hn', hn]
      rfl
    calc (ψ₁.left ≫ φ₁.φ) ≫ m.φ = ψ₁.left ≫ φ₁.φ ≫ m.φ := Category.assoc _ _ _
      _ = ψ₁.left ≫ m''.φ ≫ φ.φ := congrArg (fun z => ψ₁.left ≫ z) e
      _ = (ψ₁.left ≫ m''.φ) ≫ φ.φ := (Category.assoc _ _ _).symm
      _ = m'.φ ≫ ψ.left ≫ φ.φ := by rw [hψ₁, Category.assoc]
end

section
open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

theorem UpperTheory.Gal.LocalSmoothExtension.powComp_of :
    PowComp := by
  intro S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k
  subst hfg
  subst hφχ
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      GlobalTheory.KS.PowPB.powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]
end

section
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.kNNormal_of :
    KNNormal := by
  intro p _ D G L M
  have key : ∀ k ∈ L.KN 1, ∀ u, L.CongOne M u → L.CongOne M (k * u * k⁻¹) := by
    intro k hk u hu v hv
    obtain ⟨w, hw, e⟩ := hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)
    refine ⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩
    have h1 : L.actG k (L.actG k⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, map_nsmul, h1]
  refine ⟨fun k hk u hu => ⟨key k hk u hu.1, ?_⟩, fun hM => GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hM⟩
  have e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [e]
  exact key k hk _ hu.2
end

section
open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end

section
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaSplit_of :
    SigmaFEt → UpperTheory.Gal.G3.SplitsPts → UpperTheory.Gal.G3.PtsOfSplits → SigmaSplit := by
  intro hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs
  obtain ⟨hF1, hF2⟩ := hF Y Z s I
  obtain ⟨hsc, hiso⟩ := hs
  have hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω) := fun Ω _ =>
    inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y),
      ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y := by
    intro Ω _ y
    haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω
    obtain ⟨p⟩ := hne Ω
    obtain ⟨⟨i, a⟩, ha⟩ := (sigmaMk (fun _ : I => Y)).surjective (y.base p)
    rw [sigmaMk_mk] at ha
    refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨a, by rw [Subsingleton.elim q p]; exact ha⟩
  refine hSP _ c (I × Δ) _ ?_ ?_
  · intro z
    simp [hsc]
  · intro Ω _ _ x y hy
    obtain ⟨i, y', rfl⟩ := hpt Ω y
    have hy' : y' ≫ s = x ≫ c := by simpa using hy
    obtain ⟨δ, hδ, hδu⟩ := hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'
    refine ⟨(i, δ), ?_, ?_⟩
    · show x ≫ (σ δ ≫ _) = _
      rw [← hδ, Category.assoc]
    · rintro ⟨i', δ'⟩ h
      change x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h
      by_cases hii : i' = i
      · subst hii
        have hx : x ≫ σ δ' = y' := by
          rw [← Category.assoc] at h
          exact (cancel_mono _).1 h
        rw [hδu δ' hx]
      · haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y')
          ⟨by rw [Category.assoc]; exact h⟩ hii
        obtain ⟨p⟩ := hne Ω
        exact isEmptyElim p
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.Int.Geo (KS Lv Sc)

theorem UpperTheory.Gal.LocalSmoothExtension.kSProj_of :
    ZSm → ZPr → KSProj := by
  intro hSm hPr p _ D G L hSc gb k T N
  have hq : qAt T N = (T.e N).hom ≫ ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s) := (T.e_q N).symm
  rw [hq]
  constructor
  · obtain ⟨M, i, hi, hi'⟩ := hPr p D hSc.cpt gb N.1 N.2.1 N.2.2 (T.M N) k
    refine ⟨M, (T.e N).hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hi']
  · obtain ⟨d, hd⟩ := hSm D.toG gb N.1 N.2.1 (T.M N) k
    haveI := hd
    have h0 : SmoothOfRelativeDimension 0 (T.e N).hom := inferInstance
    have h2 := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := d) (T.e N).hom
      ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s)
    rw [zero_add] at h2
    exact ⟨d, h2⟩
end

section
namespace UpperTheory.Gal.LocalSmoothExtension

theorem HopWord_holds : HopWord := hopWord_of Tw.fnRing Tw.hopLin Tw.hopMul
theorem TransPull_holds : TransPull := transPull_of homEx_of polPull_of tatePull_of
theorem KSBc_holds : KSBc := kSBc_of (modelBc_of mapEq_of) (legBc_of mapEq_of TransPull_holds) powComp_of
theorem MemOp_holds : MemOp :=
  memOp2_of kNNormal_of cntFn_of cntSum_of sigmaFEt_of (sigmaSplit_of sigmaFEt_of Tw.splitsPts Tw.ptsOfSplits)
    Tw.twGal Tw.hopEx
theorem OccOf_holds : OccOf :=
  occOf_of MemOp_holds Tw.hodgeGood Tw.hodgeTr Tw.bcGood Tw.opBc Tw.opTr Tw.bcSplits
theorem KSProj_holds : KSProj := kSProj_of GlobalTheory.WeightTwoHeckePower.sPow_smooth GlobalTheory.WeightTwoHeckePower.isProjOver_sPow

theorem hodgeTrace_of_lefschetz_and_groupSide : HodgeTraceFromLefschetzAndGroupSide := fun hW hP hF h₁ h₂ =>
  have hT : UpperTheory.Gal.LocalSmoothExtension.HodgeTr :=
    hodgeTr_of (GroupTop_of h₁ h₂) fnDecomp_of HopWord_holds altLin_of
      (geoStep_of hW hP hF lefSum_of Tw.hodgeGood Tw.hodgeTr Tw.hopOp Tw.opTr)
      CxLin_holds Tw.hodgeGood
  have hE : HodgeEig :=
    hodgeEig_of hT hP (hodgeFin_of hW) unifBound_of hExpInj_of coeffOcc_of EigOf_holds HopWord_holds Tw.hodgeGood
  ⟨hT, hE, kSHodge_of hE KSBc_holds SpecConj_holds MemOp_holds fnDecomp_of OccOf_holds⟩

theorem ksHodge_of_inputs (hW : HolomorphicLefschetzFormula) (hF : FixK) (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) :
    UpperTheory.Gal.Int.Geo.KSHodge :=
  (hodgeTrace_of_lefschetz_and_groupSide hW KSProj_holds hF h₁ h₂).2.2

end UpperTheory.Gal.LocalSmoothExtension
end
