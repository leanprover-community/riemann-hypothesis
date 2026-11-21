import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.LeafModHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChiDetPowSplitCentre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_zero' {N : ℕ} (V : Submodule ℂ (Sm E N)) : tw V 0 = V := by
  unfold tw
  have h : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
    apply Subtype.ext; ext x
    simp [GlobalTheory.CuspRep.Model.absC, GlobalTheory.Mem.Chr.CharModel.absHom]
  rw [h]
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twPart_one (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : twPart 1 x = x := by
  obtain ⟨M, V⟩ := x
  simp only [twPart]
  congr 1
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twRep_of_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : ∀ g, χ g = 1) : twRep ρ χ = ρ := by
  ext g x
  simp [twRep_apply, hχ]

theorem Sep.equiv {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ.Equiv τ') : Sep ρ S τ' := by
  obtain ⟨hS, J, L, hL, hinj⟩ := h
  refine ⟨hS, J, fun j => e.toLinearMap ∘ₗ L j, fun j g x hx hs => ?_, fun x hx hs h0 => hinj x hx hs fun j => ?_⟩
  · simp only [LinearMap.comp_apply, hL j g x hx hs]
    exact LinearMap.congr_fun (e.isIntertwining' g) (L j x)
  · exact e.toLinearEquiv.injective ((h0 j).trans (map_zero _).symm)

theorem Sep.equiv_symm {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ'.Equiv τ) : Sep ρ S τ' :=
  h.equiv e.symm

theorem sep_of_subsingleton {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) (hG : ∀ g : G, g = 1)
    (hX : Nontrivial X) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ x ∈ S, ℓ x = 0 → x = 0) : Sep ρ S τ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  refine ⟨fun g x hx => by rw [hG g, map_one]; exact hx, Unit, fun _ => ℓ.smulRight v,
    fun _ g x _ _ => by rw [hG g, map_one, map_one]; rfl,
    fun x hx _ h0 => hℓ x hx ((smul_eq_zero.1 (h0 ())).resolve_right hv)⟩

theorem equiv_untwist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (f : a ⊕ b ≃ n)
    {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GL n k) Z) (π₁ : Representation ℂ (GL a k) X) (π₂ : Representation ℂ (GL b k) Y)
    (χ₁ : GL a k →* ℂˣ) (χ₂ : GL b k →* ℂˣ) (h₁ : ∀ g, χ₁ g = 1) (h₂ : ∀ g, χ₂ g = 1)
    (e : τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor (twRep π₁ χ₁) (twRep π₂ χ₂)))) :
    Nonempty (τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor π₁ π₂))) := by
  rw [twRep_of_one π₁ χ₁ h₁, twRep_of_one π₂ χ₂ h₂] at e
  exact ⟨e⟩

theorem sep_rank0 (w : Pl E) (S : Submodule ℂ (Sm E 0)) (P : Pre E 0) :
    Sep ((finRep E 0).comp (locGL E 0 w)) S (lp P w) := by
  refine sep_of_subsingleton _ _ _ (fun g => Units.ext (Subsingleton.elim _ _))
    (GlobalTheory.PfBCI.nontrivial_locProd P.h w (P.σ · w)) ((LinearMap.proj 1).comp (Sm E 0).subtype) ?_
  intro x _ h
  apply Subtype.ext; funext g
  obtain rfl : g = 1 := Units.ext (Subsingleton.elim _ _)
  exact h

theorem sep_leaf_pos (hL : LeafMod) (w : Pl E) {M : ℕ} (V : Submodule ℂ (Sm E M)) (hV : IsDiscrete V) (hM : 0 < M)
    (P : Pre E M) (hp : TreeParts (Tr.leaf V 0) P) : Sep ((finRep E M).comp (locGL E M w)) V (lp P w) := by
  obtain ⟨c, N, h, V', σ, m, pos, disc, loc, inf⟩ := P
  have hp' : List.ofFn (fun i => (⟨N i, V' i⟩ : Σ M, Submodule ℂ (Sm E M))) = [⟨M, V⟩] := by
    unfold TreeParts at hp
    rw [hp]
    simp [Tr.leafList, hM]
  have hc : c = 1 := by simpa using congrArg List.length hp'
  subst hc
  obtain ⟨d, rfl⟩ : ∃ d, N = fun _ => d := ⟨N 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s, rfl⟩ : ∃ s, σ = fun _ => s := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have h0 : (⟨d, V' 0⟩ : Σ M, Submodule ℂ (Sm E M)) = ⟨M, V⟩ := by simpa using hp'
  obtain ⟨rfl, hVV⟩ := Sigma.mk.inj_iff.1 h0
  obtain rfl := eq_of_heq hVV
  obtain ⟨e⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (s w).smooth (GlobalTheory.SmGL.stdBlocks (fun _ => d) h)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp))
  exact Sep.equiv (hL E d (V' 0) w (s w) (disc 0) (loc 0 w)) e

theorem sum_leafList : ∀ {N : ℕ} (t : Tr E N), ((t.leafList.filter fun x => 0 < x.1).map (·.1)).sum = N
  | M, .leaf V z => by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp [Tr.leafList]
    · simp [Tr.leafList, h]
  | _, .node t₁ t₂ => by simp [Tr.leafList, List.filter_append, sum_leafList t₁, sum_leafList t₂]

def Pre.restr {n : ℕ} (P : Pre E n) {k r : ℕ} (ι : Fin k → Fin P.c) (h : ∑ i, P.N (ι i) = r) : Pre E r where
  c := k
  N i := P.N (ι i)
  h := h
  V i := P.V (ι i)
  σ i := P.σ (ι i)
  m i := P.m (ι i)
  pos i := P.pos _
  discrete i := P.discrete _
  loc i := P.loc _
  inf i := P.inf _

theorem exists_split {n r s : ℕ} (P : Pre E n) (A B : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (hAB : parts P = A ++ B)
    (hA : (A.map (·.1)).sum = r) (hB : (B.map (·.1)).sum = s) :
    ∃ (P₁ : Pre E r) (P₂ : Pre E s), parts P₁ = A ∧ parts P₂ = B := by
  have hlen : P.c = A.length + B.length := by simpa [parts] using congrArg List.length hAB
  have key : ∀ k (hk : k < P.c), (⟨P.N ⟨k, hk⟩, P.V ⟨k, hk⟩⟩ : Σ M, Submodule ℂ (Sm E M)) =
      (A ++ B)[k]'(by simp; omega) := fun k hk => by
    have := List.getElem_of_eq hAB (i := k) (by simp [parts]; exact hk)
    simpa [parts] using this
  let ι₁ : Fin A.length → Fin P.c := fun i => ⟨i, by omega⟩
  let ι₂ : Fin B.length → Fin P.c := fun j => ⟨A.length + j, by omega⟩
  have e₁ : List.ofFn (fun i => (⟨P.N (ι₁ i), P.V (ι₁ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = A := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    exact (key k _).trans (List.getElem_append_left hk2)
  have e₂ : List.ofFn (fun i => (⟨P.N (ι₂ i), P.V (ι₂ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = B := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    refine (key _ _).trans ?_
    rw [List.getElem_append_right (by omega)]
    simp
  have s₁ : ∑ i, P.N (ι₁ i) = r := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₁
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hA, ← this]; rfl
  have s₂ : ∑ i, P.N (ι₂ i) = s := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₂
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hB, ← this]; rfl
  exact ⟨Pre.restr P ι₁ s₁, Pre.restr P ι₂ s₂, e₁, e₂⟩

theorem tree_module_separation (hL : LeafMod) (hN : NodeMod) (hJ : JoinMod) (w : Pl E) :
    ∀ {N : ℕ} (t : Tr E N) (P : Pre E N), t.Good → t.Untw → TreeParts t P →
      Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w) := by
  intro N t
  induction t with
  | leaf V z =>
    intro P hg hu hp
    have hz : z = 0 := hu z (by simp [Tr.twists])
    subst hz
    show Sep _ (tw V 0) _
    rw [tw_zero']
    rcases hg with ⟨hM, -, -⟩ | ⟨hM, hV, -⟩
    · subst hM; exact sep_rank0 w V P
    · exact sep_leaf_pos hL w V hV hM P hp
  | node t₁ t₂ ih₁ ih₂ =>
    intro P hg hu hp
    obtain ⟨g₁, g₂⟩ := hg
    have u₁ : t₁.Untw := fun z hz => hu z (List.mem_append_left _ hz)
    have u₂ : t₂.Untw := fun z hz => hu z (List.mem_append_right _ hz)
    have hp' : parts P = (t₁.leafList.filter fun x => 0 < x.1) ++ (t₂.leafList.filter fun x => 0 < x.1) := by
      rw [← List.filter_append]; exact hp
    obtain ⟨P₁, P₂, h₁, h₂⟩ := exists_split P _ _ hp' (sum_leafList t₁) (sum_leafList t₂)
    have hj : IsJoin 1 1 P₁ P₂ P := by
      unfold IsJoin
      rw [hp', h₁, h₂]
      have : twPart (E := E) 1 = id := funext twPart_one
      rw [this, List.map_id, List.map_id]
    obtain ⟨e⟩ := equiv_untwist (e := (hJ E _ _ _ rfl 1 1 P₁ P₂ P w hj).some)
      (h₁ := fun _ => by simp only [MonoidHom.comp_apply, HChar.loc_one])
      (h₂ := fun _ => by simp only [MonoidHom.comp_apply, HChar.loc_one])
    exact Sep.equiv_symm (hN E _ _ t₁ t₂ w _ _ _ _ (ih₁ P₁ g₁ u₁ h₁) (ih₂ P₂ g₂ u₂ h₂)) e

theorem treeModOf_holds : TreeModOf :=
  fun hL hN hJ _ _ _ _ _ t P w hg hu hp => tree_module_separation hL hN hJ w t P hg hu hp

end PositivityTheory.Rg.BcB.F.RS

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

def prodT (A : Submodule ℂ P1) (B : Submodule ℂ P2) : A ⊗[ℂ] B →ₗ[ℂ] (Y1 × Y2 → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun (u : A) (v : B) (x : Y1 × Y2) => u.1.1 x.1 * v.1.1 x.2)
    (fun u u' v => by funext x; simp [add_mul])
    (fun c u v => by funext x; simp [mul_assoc])
    (fun u v v' => by funext x; simp [mul_add])
    (fun c u v => by funext x; simp; ring))

@[simp] theorem prodT_tmul (A : Submodule ℂ P1) (B : Submodule ℂ P2) (u : A) (v : B) :
    prodT A B (u ⊗ₜ v) = fun x => u.1.1 x.1 * v.1.1 x.2 := rfl

theorem prodT_sum (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} (s : Finset κ) (x : κ → A) (y : κ → B) :
    prodT A B (∑ k ∈ s, x k ⊗ₜ y k) = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
  funext z
  simp [map_sum, Finset.sum_apply]

theorem linInd {Y : Type} {P : Submodule ℂ (Y → ℂ)} {A : Submodule ℂ P} {κ : Type} (b : Module.Basis κ ℂ A) :
    LinearIndependent ℂ (fun k => (b k).1.1) :=
  b.linearIndependent.map' (P.subtype ∘ₗ A.subtype)
    (LinearMap.ker_eq_bot.2 fun _ _ h => Subtype.ext (Subtype.ext h))

theorem coeff_zero {κ : Type} (b : κ → Y2 → ℂ) (hb : LinearIndependent ℂ b) (s : Finset κ) (c : κ → Y1 → ℂ)
    (h : ∀ y1 y2, ∑ k ∈ s, c k y1 * b k y2 = 0) : ∀ k ∈ s, c k = 0 := by
  intro k hk
  funext y1
  exact linearIndependent_iff'.1 hb s (fun k => c k y1)
    (by funext y2; simpa [Finset.sum_apply] using h y1 y2) k hk

theorem expR (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℂ B)
    (t : A ⊗[ℂ] B) :
    prodT A B t = fun x => ∑ k ∈ (TensorProduct.equivFinsuppOfBasisRight b t).support,
      ((TensorProduct.equivFinsuppOfBasisRight b t) k).1.1 x.1 * (b k).1.1 x.2 := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply t]
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum, prodT_sum]

theorem expL (A : Submodule ℂ P1) (B : Submodule ℂ P2) {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℂ A)
    (t : A ⊗[ℂ] B) :
    prodT A B t = fun x => ∑ k ∈ (TensorProduct.equivFinsuppOfBasisLeft b t).support,
      (b k).1.1 x.1 * ((TensorProduct.equivFinsuppOfBasisLeft b t) k).1.1 x.2 := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, prodT_sum]

end ReadingModuleProducts

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2] [Monoid Y1] [Monoid Y2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (v : V) : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u.1 u.2

theorem decomp (e1 : G1 →* Y1) (e2 : G2 →* Y2) (ρ1 : Representation ℂ G1 P1) (ρ2 : Representation ℂ G2 P2)
    (hρ1 : ∀ g v y, (ρ1 g v).1 y = v.1 (y * e1 g)) (hρ2 : ∀ g v y, (ρ2 g v).1 y = v.1 (y * e2 g))
    (S1 : Submodule ℂ P1) (S2 : Submodule ℂ P2) (U1 : Subgroup G1) (U2 : Subgroup G2) (t : S1 ⊗[ℂ] S2)
    (hU1 : ∀ u ∈ U1, ∀ x : Y1 × Y2, prodT S1 S2 t (x.1 * e1 u, x.2) = prodT S1 S2 t x)
    (hU2 : ∀ u ∈ U2, ∀ x : Y1 × Y2, prodT S1 S2 t (x.1, x.2 * e2 u) = prodT S1 S2 t x) :
    ∃ (κ : Type) (s : Finset κ) (x : κ → S1) (y : κ → S2), (∀ k, (x k).1 ∈ fixed ρ1 U1) ∧
      (∀ k, (y k).1 ∈ fixed ρ2 U2) ∧ LinearIndependent ℂ (fun k => (x k).1.1) ∧
      prodT S1 S2 t = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
  classical
  set b2 := Module.Basis.ofVectorSpace ℂ S2
  set m := TensorProduct.equivFinsuppOfBasisRight b2 t
  have hx := expR S1 S2 b2 t
  have hfix : ∀ k, (m k).1 ∈ fixed ρ1 U1 := by
    intro k
    rw [mem_fixed_iff]
    intro u hu
    by_cases hk : k ∈ m.support
    · have := coeff_zero (fun k => (b2 k).1.1) (linInd b2) m.support
        (fun k y1 => (m k).1.1 (y1 * e1 u) - (m k).1.1 y1) (fun y1 y2 => by
          have h := hU1 u hu (y1, y2)
          rw [hx] at h
          simp only [sub_mul, Finset.sum_sub_distrib]
          exact sub_eq_zero.2 h) k hk
      apply Subtype.ext
      funext y
      rw [hρ1]
      exact sub_eq_zero.1 (congrFun this y)
    · rw [Finsupp.notMem_support_iff.1 hk]
      simp
  set A1 : Submodule ℂ P1 := S1 ⊓ fixed ρ1 U1
  let t' : A1 ⊗[ℂ] S2 := ∑ k ∈ m.support, (⟨(m k).1, Submodule.mem_inf.2 ⟨(m k).2, hfix k⟩⟩ : A1) ⊗ₜ b2 k
  have ht' : prodT A1 S2 t' = prodT S1 S2 t := by
    rw [hx, prodT_sum]
  set b1 := Module.Basis.ofVectorSpace ℂ A1
  set n := TensorProduct.equivFinsuppOfBasisLeft b1 t'
  have hy := expL A1 S2 b1 t'
  rw [ht'] at hy
  refine ⟨_, n.support, fun l => ⟨(b1 l).1, (Submodule.mem_inf.1 (b1 l).2).1⟩, n, fun l => (Submodule.mem_inf.1 (b1 l).2).2,
    ?_, linInd b1, hy⟩
  intro l
  rw [mem_fixed_iff]
  intro u hu
  by_cases hl : l ∈ n.support
  · have := coeff_zero (fun l => (b1 l).1.1) (linInd b1) n.support
      (fun l y2 => (n l).1.1 (y2 * e2 u) - (n l).1.1 y2) (fun y2 y1 => by
        have h := hU2 u hu (y1, y2)
        rw [hy] at h
        simp only [sub_mul, Finset.sum_sub_distrib]
        refine sub_eq_zero.2 ?_
        simpa only [mul_comm] using h) l hl
    apply Subtype.ext
    funext y
    rw [hρ2]
    exact sub_eq_zero.1 (congrFun this y)
  · rw [Finsupp.notMem_support_iff.1 hl]
    simp

end ReadingModuleProducts

namespace ReadingModuleProducts

variable {G1 G2 Y1 Y2 : Type} [Group G1] [Group G2] [Monoid Y1] [Monoid Y2]
  {P1 : Submodule ℂ (Y1 → ℂ)} {P2 : Submodule ℂ (Y2 → ℂ)}

theorem sep_pair [TopologicalSpace G1] [TopologicalSpace G2] {X1 X2 : Type} [AddCommGroup X1] [Module ℂ X1]
    [AddCommGroup X2] [Module ℂ X2] (e1 : G1 →* Y1) (e2 : G2 →* Y2) (ρ1 : Representation ℂ G1 P1)
    (ρ2 : Representation ℂ G2 P2) (hρ1 : ∀ g v y, (ρ1 g v).1 y = v.1 (y * e1 g))
    (hρ2 : ∀ g v y, (ρ2 g v).1 y = v.1 (y * e2 g)) (ρ : Representation ℂ (G1 × G2) (Y1 × Y2 → ℂ))
    (hρ : ∀ g F x, ρ g F x = F (x.1 * e1 g.1, x.2 * e2 g.2)) (S1 : Submodule ℂ P1) (S2 : Submodule ℂ P2)
    (τ1 : Representation ℂ G1 X1) (τ2 : Representation ℂ G2 X2) (h1 : Sep ρ1 S1 τ1) (h2 : Sep ρ2 S2 τ2) :
    Sep ρ (Submodule.span ℂ {F | ∃ φ₁ ∈ S1, ∃ φ₂ ∈ S2, F = fun x => φ₁.1 x.1 * φ₂.1 x.2})
      (GlobalTheory.SmGL.extTensor τ1 τ2) := by
  classical
  obtain ⟨hs1, J1, L1, heq1, hsep1⟩ := h1
  obtain ⟨hs2, J2, L2, heq2, hsep2⟩ := h2
  have hR : Submodule.span ℂ {F | ∃ φ₁ ∈ S1, ∃ φ₂ ∈ S2, F = fun x => φ₁.1 x.1 * φ₂.1 x.2} =
      LinearMap.range (prodT S1 S2) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro F ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      exact ⟨(⟨φ₁, h₁⟩ : S1) ⊗ₜ (⟨φ₂, h₂⟩ : S2), rfl⟩
    · rintro F ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v => exact Submodule.subset_span ⟨u.1, u.2, v.1, v.2, rfl⟩
      | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'
  rw [hR]
  set Ψ := prodT S1 S2
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    rw [LinearMap.mem_ker] at ht
    set b2 := Module.Basis.ofVectorSpace ℂ S2
    set m := TensorProduct.equivFinsuppOfBasisRight b2 t
    have hx := expR S1 S2 b2 t
    rw [ht] at hx
    have hz := coeff_zero (fun k => (b2 k).1.1) (linInd b2) m.support (fun k => (m k).1.1)
      (fun y1 y2 => (congrFun hx (y1, y2)).symm)
    have hm : m = 0 := by
      ext k : 1
      by_cases hk : k ∈ m.support
      · exact Subtype.ext (Subtype.ext (hz k hk))
      · exact Finsupp.notMem_support_iff.1 hk
    have : t = (TensorProduct.equivFinsuppOfBasisRight b2).symm m := by simp [m]
    rw [this, hm, map_zero]
  set e := LinearEquiv.ofInjective Ψ hinj
  have hL : ∀ j : J1 × J2, ∃ g : (Y1 × Y2 → ℂ) →ₗ[ℂ] X1 ⊗[ℂ] X2, g ∘ₗ (LinearMap.range Ψ).subtype =
      (TensorProduct.map (L1 j.1 ∘ₗ S1.subtype) (L2 j.2 ∘ₗ S2.subtype)) ∘ₗ e.symm.toLinearMap :=
    fun j => LinearMap.exists_extend _
  choose L hLs using hL
  have spec : ∀ j t, L j (Ψ t) = TensorProduct.map (L1 j.1 ∘ₗ S1.subtype) (L2 j.2 ∘ₗ S2.subtype) t := by
    intro j t
    have h := LinearMap.congr_fun (hLs j) (e t)
    simpa [e] using h
  have specS : ∀ j {κ : Type} (s : Finset κ) (x : κ → S1) (y : κ → S2),
      L j (fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2) = ∑ k ∈ s, L1 j.1 (x k).1 ⊗ₜ L2 j.2 (y k).1 := by
    intro j κ s x y
    rw [← prodT_sum, spec]
    simp [map_sum]

  have hdec : ∀ G ∈ LinearMap.range Ψ, SmVec ρ G → ∃ (U1 : Subgroup G1) (U2 : Subgroup G2) (κ : Type) (s : Finset κ)
      (x : κ → S1) (y : κ → S2), IsOpen (U1 : Set G1) ∧ IsOpen (U2 : Set G2) ∧ (∀ k, (x k).1 ∈ fixed ρ1 U1) ∧
      (∀ k, (y k).1 ∈ fixed ρ2 U2) ∧ LinearIndependent ℂ (fun k => (x k).1.1) ∧
      G = fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2 := by
    rintro G ⟨t, rfl⟩ ⟨U, hUo, hU⟩
    rw [mem_fixed_iff] at hU
    obtain ⟨κ, s, x, y, hx, hy, hli, hG⟩ := decomp e1 e2 ρ1 ρ2 hρ1 hρ2 S1 S2 (U.comap (MonoidHom.inl G1 G2))
      (U.comap (MonoidHom.inr G1 G2)) t
      (fun u hu z => by simpa [hρ] using congrFun (hU (u, 1) hu) z)
      (fun u hu z => by simpa [hρ] using congrFun (hU (1, u) hu) z)
    exact ⟨_, _, κ, s, x, y, hUo.preimage (continuous_id.prodMk continuous_const),
      hUo.preimage (continuous_const.prodMk continuous_id), hx, hy, hli, hG⟩
  refine ⟨?_, J1 × J2, L, ?_, ?_⟩
  · intro g G hG
    obtain ⟨t, rfl⟩ := hG
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      refine ⟨(⟨ρ1 g.1 u.1, hs1 g.1 u.1 u.2⟩ : S1) ⊗ₜ (⟨ρ2 g.2 v.1, hs2 g.2 v.1 v.2⟩ : S2), ?_⟩
      funext z
      simp [Ψ, hρ, hρ1, hρ2]
    | add t t' ht ht' => rw [map_add, map_add]; exact add_mem ht ht'
  · intro j g G hG hsm
    obtain ⟨U1, U2, κ, s, x, y, hU1o, hU2o, hx, hy, -, rfl⟩ := hdec G hG hsm
    have hG' : ρ g (fun z => ∑ k ∈ s, (x k).1.1 z.1 * (y k).1.1 z.2) =
        fun z => ∑ k ∈ s, ((⟨ρ1 g.1 (x k).1, hs1 g.1 _ (x k).2⟩ : S1)).1.1 z.1 *
          ((⟨ρ2 g.2 (y k).1, hs2 g.2 _ (y k).2⟩ : S2)).1.1 z.2 := by
      funext z
      simp [hρ, hρ1, hρ2]
    rw [hG', specS, specS, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [heq1 j.1 g.1 _ (x k).2 ⟨U1, hU1o, hx k⟩, heq2 j.2 g.2 _ (y k).2 ⟨U2, hU2o, hy k⟩, GlobalTheory.SmGL.extTensor_tmul]
  · intro G hG hsm h0
    obtain ⟨U1, U2, κ, s, x, y, hU1o, hU2o, hx, hy, hli, rfl⟩ := hdec G hG hsm
    have hy0 : ∀ k ∈ s, y k = 0 := by
      intro k hk
      apply Subtype.ext
      refine hsep2 _ (y k).2 ⟨U2, hU2o, hy k⟩ fun j2 => ?_
      rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
      intro β
      set c : κ → ℂ := fun k => β (L2 j2 (y k).1) with hc
      have hw : ∑ k ∈ s, c k • (x k).1 = 0 := by
        refine hsep1 _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (x k).2)
          ⟨U1, hU1o, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)⟩ fun j1 => ?_
        have h := congrArg (fun u => TensorProduct.rid ℂ X1 (LinearMap.lTensor X1 β u)) (h0 (j1, j2))
        simp only [specS, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at h
        simpa [map_sum, hc] using h
      exact linearIndependent_iff'.1 hli s c (by
        have := congrArg (fun v : P1 => v.1) hw
        simpa using this) k hk
    funext z
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hy0 k hk]
    simp

end ReadingModuleProducts

theorem readModOf_holds : ReadModOf := by
  intro hT E _ _ _ a b s₁ s₂ Pa Pb w g₁ g₂ u₁ u₂ t₁ t₂
  exact ReadingModuleProducts.sep_pair (embW a w) (embW b w) ((finRep E a).comp (locGL E a w))
    ((finRep E b).comp (locGL E b w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (pairRt a b w) (fun _ _ _ => rfl)
    s₁.space s₂.space _ _ (hT E a s₁ Pa w g₁ u₁ t₁) (hT E b s₂ Pb w g₂ u₂ t₂)

end PositivityTheory.Rg.BcB.F.RS

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

theorem tso_map_heckeVec {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G X} {K : Subgroup G} {h : G → ℂ} (hK : IsCommensurated K)
    (hh : h ∈ Hecke ℂ K) (L : V →ₗ[ℂ] X) {x : V} (hL : ∀ g, L (ρ g x) = τ g (L x)) :
    L (heckeVec ρ K h x) = heckeVec τ K h (L x) := by
  refine (L.toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => ?_)
  simp [hL]

theorem tso_heckeVec_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} (S : Submodule ℂ V) (hS : ∀ g, ∀ y ∈ S, ρ g y ∈ S) {x : V} (hx : x ∈ S) :
    heckeVec ρ K h x ∈ S := by
  unfold heckeVec
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun c => S.smul_mem _ (hS _ _ hx)

theorem tso_heckeVec_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

theorem treeSatOf_holds : TreeSatOf := by
  intro hT E _ _ _ N t P w hg hu htp ⟨φ0, hφ0S, hφ00, hφ0K⟩
  obtain ⟨hinv, J, L, heq, hsep⟩ := hT E N t P w hg hu htp
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w N).1
  have hKc := Final.GLintComm E w N
  have fixK : ∀ φ, (∀ k ∈ KGL w N, finRep E N (locGL E N w k) φ = φ) →
      φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w N) :=
    fun φ h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => h k hk
  have smK : ∀ φ, φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w N) → SmVec ((finRep E N).comp (locGL E N w)) φ :=
    fun φ h => ⟨_, hKo, h⟩
  have hLfix : ∀ j φ, φ ∈ t.space → φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w N) →
      L j φ ∈ fixed (lp P w) (KGL w N) := fun j φ hS hf =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← heq j k φ hS (smK _ hf), GlobalTheory.LGrp.mem_fixed.1 hf k hk]
  obtain ⟨j, hj⟩ : ∃ j, L j φ0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ00 (hsep φ0 hφ0S (smK _ (fixK _ hφ0K)) hc)
  obtain ⟨b, hb, -⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ) (fun i => (P.σ i w).smooth)
    (fun i => (P.σ i w).irred) (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj
  have hvec : ∀ f ∈ fixed (lp P w) (KGL w N), f ≠ 0 → IsSatVecGL w (lp P w) f (∑ i, b i) := fun f hf hf0 => by
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ)
      (fun i => (P.σ i w).smooth) (fun i => (P.σ i w).irred) hf hf0
    have e : S = b := funext fun a => (hS a).unique (hb a)
    rw [← e]
    exact hfS
  have hcard : (∑ i, b i).card = N := (hvec _ (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj).2.2.1
  refine ⟨_, ⟨b, fun i => ⟨(hb i).1, hb i⟩, rfl⟩, fun φ hφS hφ0 hφK => ?_⟩
  have hf := fixK _ hφK
  refine ⟨hφ0, hf, hcard, fun ϖ hϖ i hi => ?_⟩
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := N) hϖ i
  have hTS := tso_heckeVec_mem (K := KGL w N) (h := Tj ℂ N (Ov E w) ϖ i) t.space hinv hφS
  have hTf := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed hKc hh hf
  refine sub_eq_zero.1 (hsep _ (t.space.sub_mem hTS (t.space.smul_mem _ hφS))
    (smK _ (sub_mem hTf (Submodule.smul_mem _ _ hf))) fun j' => ?_)
  have key := tso_map_heckeVec (τ := lp P w) hKc hh (L j') fun g => heq j' g φ hφS (smK _ hf)
  rw [LinearMap.map_sub, LinearMap.map_smul]
  refine sub_eq_zero.2 (key.trans ?_)
  by_cases h0 : L j' φ = 0
  · exact (congrArg (heckeVec (lp P w) (KGL w N) (Tj ℂ N (Ov E w) ϖ i)) h0).trans
      (tso_heckeVec_zero.trans ((smul_zero _).symm.trans (congrArg _ h0.symm)))
  · exact (hvec _ (hLfix j' φ hφS hf) h0).2.2.2 ϖ hϖ i hi

end PositivityTheory.Rg.BcB.F.RS

end
end

section
namespace PositivityTheory.Rg.BcB.F.RS

theorem joinEx_holds : JoinEx := GlobalTheory.CompanionTheory.JoinDatum.joinEx

theorem joinInf_holds : JoinInf := GlobalTheory.CompanionTheory.JoinInfProof.joinInf

theorem joinSat_holds : JoinSat := GlobalTheory.CompanionTheory.JoinSatPf.joinSat

theorem treeInf_holds : TreeInf := GlobalTheory.CompanionTheory.TreeInfSum.treeInf

theorem weightJoin_holds : WeightJoin := GlobalTheory.CompanionTheory.WeightJoin.main

theorem muLoc_holds' : MuLoc := GlobalTheory.CompanionTheory.MuLocal.muLoc_holds

theorem treeMod_of (h : JoinMod) : TreeMod := treeModOf_holds leafMod_holds GlobalTheory.CompanionTheory.NodeSep.nodeMod h

theorem readMod_of (h : JoinMod) : ReadMod := readModOf_holds (treeMod_of h)

theorem readSplit_of_join (h : JoinMod) : ReadSplit :=
  readSplit_of (treeSatOf_holds (treeMod_of h)) pairSat_holds thetaSat2_holds GlobalTheory.CompanionTheory.CtS.ctSat muLoc_holds' joinSat_holds
    GlobalTheory.CompanionTheory.SatSplitAt.satSplit GlobalTheory.CompanionTheory.ConjSat.satConj

end PositivityTheory.Rg.BcB.F.RS
end

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace PositivityTheory.Rg.BcB.F.RS.JB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

structure RB (N : ℕ) : Type 1 where
  V : Type
  [ag : AddCommGroup V]
  [md : Module ℂ V]
  ρ : Representation ℂ (GL (Fin N) k) V
  sm : IsSmooth ρ

attribute [instance] RB.ag RB.md

def Iso {N : ℕ} (A B : RB k N) : Prop := Nonempty (A.ρ.Equiv B.ρ)

theorem Iso.refl {N : ℕ} (A : RB k N) : Iso A A := ⟨.refl _⟩

theorem Iso.symm {N : ℕ} {A B : RB k N} (h : Iso A B) : Iso B A := h.elim fun a => ⟨a.symm⟩

theorem Iso.trans {N : ℕ} {A B C : RB k N} (h : Iso A B) (h' : Iso B C) : Iso A C := by
  exact eqv_trans h h'

def one (u : IrrGL k) : RB k u.1 := ⟨_, u.rep, u.2.rep.smooth⟩

def mp {c N : ℕ} (z : Fin c → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) : RB k N :=
  ⟨_, multiProd e fun a => (z a).rep, isSmooth_parInd _ _⟩

def i2 {r t N : ℕ} (h : r + t = N) (A : RB k r) (B : RB k t) : RB k N :=
  ⟨_, ind₂ (stdSum h) (extTensor A.ρ B.ρ), isSmooth_parInd _ _⟩

theorem parabolic_induction_congr {r t N : ℕ} (h : r + t = N) {A A' : RB k r} {B B' : RB k t} (a : Iso A A') (b : Iso B B') :
    Iso (i2 h A B) (i2 h A' B') := ind₂_congr h (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := B.ρ) (σ₂ := B'.ρ) a b

theorem parabolic_induction_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : RB k r) (B : RB k s) (C : RB k t) : Iso (i2 h₂ (i2 h₁ A B) C) (i2 h₄ A (i2 h₃ B C)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ B.ρ C.ρ A.sm B.sm C.sm

theorem mp_placing {c N : ℕ} (z : Fin c → IrrGL k) (e e' : (Σ a, Fin (z a).1) ≃ Fin N) : Iso (mp z e) (mp z e') :=
  multiProd_placing e e' fun a => (z a).rep

theorem mp_head {c T N : ℕ} (z : Fin (c + 1) → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) (h : (z 0).1 + T = N)
    (e' : (Σ a : Fin c, Fin (z a.succ).1) ≃ Fin T) : Iso (mp z e) (i2 h (one (z 0)) (mp (fun a => z a.succ) e')) :=
  multiProd_head (k := k) (fun a => (z a).rep) e h e'

theorem parabolic_induction_unit {r t : ℕ} (h : t + r = r) (A : RB k r) (x : Fin 0 → IrrGL k) (e : (Σ a, Fin (x a).1) ≃ Fin t) :
    Iso (i2 h (mp x e) A) A :=
  ind₂_unit_left k r t h A.V A.ρ A.sm (fun a => (x a).1) _ (fun a => (x a).rep) e

theorem card_eq {c N : ℕ} (z : Fin c → IrrGL k) (e : (Σ a, Fin (z a).1) ≃ Fin N) : ∑ a, (z a).1 = N := by
  simpa using Fintype.card_congr e

theorem ex_e {c : ℕ} (z : Fin c → IrrGL k) : ∃ N, Nonempty ((Σ a, Fin (z a).1) ≃ Fin N) := ⟨_, ⟨finSigmaFinEquiv⟩⟩

attribute [irreducible] Iso one mp i2

theorem head_congr {u u' : IrrGL k} (hu : u = u') {T N : ℕ} (h : u.1 + T = N) (h' : u'.1 + T = N) (B : RB k T) :
    Iso (i2 h (one u) B) (i2 h' (one u') B) := by
  subst hu
  exact Iso.refl _

theorem stagesB : ∀ (s₁ s₂ c : ℕ) (z : Fin c → IrrGL k) (x : Fin s₁ → IrrGL k) (y : Fin s₂ → IrrGL k),
    List.ofFn z = List.ofFn x ++ List.ofFn y → ∀ {N r t : ℕ} (h : r + t = N) (e : (Σ a, Fin (z a).1) ≃ Fin N)
      (e₁ : (Σ a, Fin (x a).1) ≃ Fin r) (e₂ : (Σ a, Fin (y a).1) ≃ Fin t), Iso (mp z e) (i2 h (mp x e₁) (mp y e₂)) := by
  intro s₁
  induction s₁ with
  | zero =>
    intro s₂ c z x y hz N r t h e e₁ e₂
    have hr : r = 0 := by
      have := Fintype.card_congr e₁
      simpa using this.symm
    subst hr
    have hN : N = t := by omega
    subst hN
    have hzy : List.ofFn z = List.ofFn y := by simpa using hz
    rw [List.ofFn_inj'] at hzy
    cases hzy
    exact Iso.trans (mp_placing _ e e₂) (Iso.symm (parabolic_induction_unit h _ x e₁))
  | succ n ih =>
    intro s₂ c z x y hz N r t h e e₁ e₂
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := by
      cases c with
      | zero => simp [List.ofFn_succ] at hz
      | succ c' => exact ⟨c', rfl⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.cons_append] at hz
    obtain ⟨h0, htail⟩ := List.cons.inj hz
    obtain ⟨T, ⟨e'⟩⟩ := ex_e (fun a : Fin c' => z a.succ)
    obtain ⟨r', ⟨e₁'⟩⟩ := ex_e (fun a : Fin n => x a.succ)
    have hT : (z 0).1 + T = N := by
      have h1 := card_eq z e
      have h2 := card_eq _ e'
      rw [Fin.sum_univ_succ] at h1
      omega
    have hr' : (x 0).1 + r' = r := by
      have h1 := card_eq x e₁
      have h2 := card_eq _ e₁'
      rw [Fin.sum_univ_succ] at h1
      omega
    have hT' : r' + t = T := by
      rw [h0] at hT
      omega
    have h₁ : (z 0).1 + r' = r := by
      rw [h0]
      exact hr'
    have s1 := mp_head z e hT e'
    have s2 := parabolic_induction_congr hT (Iso.refl (one (z 0))) (ih s₂ c' (fun a => z a.succ) (fun a => x a.succ) y htail hT' e' e₁' e₂)
    have s3 := Iso.symm (parabolic_induction_assoc h₁ h hT' hT (one (z 0)) (mp (fun a => x a.succ) e₁') (mp y e₂))
    have s4 : Iso (i2 h₁ (one (z 0)) (mp (fun a => x a.succ) e₁')) (mp x e₁) :=
      Iso.trans (head_congr h0 h₁ hr' _) (Iso.symm (mp_head x e₁ hr' e₁'))
    have s5 := parabolic_induction_congr h s4 (Iso.refl (mp y e₂))
    exact Iso.trans s1 (Iso.trans s2 (Iso.trans s3 s5))

end PositivityTheory.Rg.BcB.F.RS.JB

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS.JB

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twCongr' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twRep ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (φ v)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (φ.isIntertwining' g) v

unseal Iso i2 in
theorem fin_step {r t N : ℕ} (h : r + t = N) {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (ρ₀ : Representation ℂ (GL (Fin N) k) V₀) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin t) k) V₂) (A₀ : RB k N) (A : RB k r) (B : RB k t) (e₀ : Nonempty (ρ₀.Equiv A₀.ρ))
    (e₁ : Nonempty (ρ₁.Equiv A.ρ)) (e₂ : Nonempty (ρ₂.Equiv B.ρ)) (hI : Iso A₀ (i2 h A B)) :
    Nonempty (ρ₀.Equiv (ind₂ (stdSum h) (extTensor ρ₁ ρ₂))) := by
  have a : Nonempty (A₀.ρ.Equiv (ind₂ (stdSum h) (extTensor A.ρ B.ρ))) := hI
  exact e₀.elim fun x => a.elim fun y => (ind₂_congr h e₁ e₂).elim fun z => ⟨(x.trans y).trans z.symm⟩

unseal mp in
theorem to_mp {c N : ℕ} (z : Fin c → IrrGL k) (h : ∑ a, (z a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (e : Nonempty (ρ.Equiv (prodIrr z h))) :
    Nonempty (ρ.Equiv (mp z (stdBlocks (fun a => (z a).1) h)).ρ) := e

end Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locComp_unique' {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ)
    (h' : IsLocCompGL V w σ') : Nonempty (σ.ρ.Equiv σ'.ρ) := by
  have hst : ∀ g, ∀ φ ∈ V, finRep E a (locGL E a w g) φ ∈ V := fun g φ hφ => hV.stable (.fin _) φ hφ
  let ρV : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
    { toFun := fun g => (finRep E a (locGL E a w g)).restrict (hst g)
      map_one' := LinearMap.ext fun φ => Subtype.ext (by simp)
      map_mul' := fun g g' => LinearMap.ext fun φ => Subtype.ext (by simp) }
  have := σ.irred
  have := σ'.irred
  obtain ⟨f', h0', h1', h2'⟩ := h'
  refine LocUniq.equiv_of_isoPart σ.ρ σ'.ρ ρV ?_ ⟨f'.codRestrict V h1', fun g => LinearMap.ext fun v =>
    Subtype.ext (h2' g v)⟩ fun e => h0' (LinearMap.ext fun v => by
      have := congrArg (fun F : σ'.ρ.IntertwiningMap ρV => (F.toLinearMap v : Sm E a)) e
      simpa using this)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x.1 ∈ ⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1 := by
    rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w σ h]; exact x.2
  have hle : (⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1) ≤
      (LocUniq.isoPart σ.ρ ρV).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, Submodule.mem_iSup_of_mem (⟨f.1.codRestrict V f.2.1, fun g => LinearMap.ext fun u =>
      Subtype.ext (f.2.2 g u)⟩ : σ.ρ.IntertwiningMap ρV) ⟨v, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

theorem of_eq_of_locComp' {w : HeightOneSpectrum (𝓞 E)} {x y : Σ M : ℕ, Submodule ℂ (Sm E M)}
    (hxy : x = y) (hV : IsDiscrete x.2) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (h : IsLocCompGL x.2 w σ) (h' : IsLocCompGL y.2 w σ') :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  subst hxy
  exact IrrGL.of_eq_of.2 (locComp_unique' hV h h')

def twLoc {w : HeightOneSpectrum (𝓞 E)} {M : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin M) (w.adicCompletion E)) V) (χ : HChar E) :
    (twRep ρ (CuspSub.locDet M χ w)).Equiv (twist ρ (GlobalTheory.SmGL.detChar (Fin M) (χ.loc w))) :=
  .mk (LinearEquiv.refl ℂ V) fun _ => LinearMap.ext fun _ => rfl

def twCls {m : ℕ} (χ : HChar E) (P : Pre E m) (w : HeightOneSpectrum (𝓞 E)) :
    Fin P.c → IrrGL (w.adicCompletion E) :=
  fun j => (P.cls j w).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w)

theorem cls_tw {n M : ℕ} (D : Pre E n) (i : Fin D.c) (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)}
    (V : Submodule ℂ (Sm E M)) (σ : SmIrr (GL (Fin M) (w.adicCompletion E))) (hσ : IsLocCompGL V w σ)
    (hi : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) = twPart χ ⟨M, V⟩) :
    D.cls i w = (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  rw [IrrGL.tw_of]
  have h1 := of_eq_of_locComp' hi (D.discrete i) (D.σ i w)
    (σ.twist (CuspSub.locDet M χ w) (CuspSub.isOpen_ker_locDet χ w)) (D.loc i w)
    (TwistDisc.isLocCompGL_map χ hσ)
  exact h1.trans (IrrGL.of_eq_of.2 ⟨twLoc σ.ρ χ⟩)

theorem join_parts {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n}
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) : ∃ hc : D.c = Pa.c + Pb.c, ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i := by
  have e : List.ofFn (fun i => (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      List.ofFn (Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩)) := by
    have hJ' : parts D = (parts Pa).map (twPart χ₁) ++ (parts Pb).map (twPart χ₂) := hJ
    unfold parts at hJ'
    rw [hJ', List.map_ofFn, List.map_ofFn, List.ofFn_fin_append]
    rfl
  obtain ⟨hc, hf⟩ := Sigma.mk.inj_iff.1 (List.ofFn_inj'.1 e)
  exact ⟨hc, fun i => (Fin.heq_fun_iff hc).1 hf (Fin.cast hc.symm i)⟩

theorem cls_append {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hc : D.c = Pa.c + Pb.c) (hD : ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i) :
    ∀ i, Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w := by
  intro i
  refine Fin.addCases (motive := fun i =>
    Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have hi := hD (Fin.castAdd Pb.c j)
    rw [Fin.append_left] at hi
    exact (cls_tw D _ χ₁ (Pa.V j) (Pa.σ j w) (Pa.loc j w) hi).symm
  · rw [Fin.append_right]
    have hi := hD (Fin.natAdd Pa.c j)
    rw [Fin.append_right] at hi
    exact (cls_tw D _ χ₂ (Pb.V j) (Pb.σ j w) (Pb.loc j w) hi).symm

theorem twist_lp {a : ℕ} (χ : HChar E) (P : Pre E a) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((twRep (lp P w) ((χ.loc w).comp GeneralLinearGroup.det)).Equiv (prodIrr (twCls χ P w) P.h)) :=
  ⟨(twCongr' (prodIrrEquiv P.h (fun j => (P.σ j w).ρ) (fun j => (P.σ j w).smooth)
    fun j => (P.σ j w).irred) _).trans
    (prodIrrTwistEquiv (fun j => P.cls j w) P.h (χ.loc w) (ParLaws.isSmoothChar_loc χ w))⟩

theorem lp_equiv {n : ℕ} (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((lp D w).Equiv (prodIrr (fun i => D.cls i w) D.h)) :=
  ⟨prodIrrEquiv D.h (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) fun i => (D.σ i w).irred⟩

theorem cls_list {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) :
    List.ofFn (fun i => D.cls i w) = List.ofFn (twCls χ₁ Pa w) ++ List.ofFn (twCls χ₂ Pb w) := by
  obtain ⟨hc, hD⟩ := join_parts hJ
  rw [← List.ofFn_fin_append, List.ofFn_congr hc]
  exact congrArg List.ofFn (funext fun i => (cls_append w hc hD i).symm)

theorem joinMod_holds : JoinMod := fun _ _ _ _ _ _ _ h χ₁ χ₂ Pa Pb D w hJ =>
  fin_step h _ _ _ _ _ _ (to_mp (fun i => D.cls i w) D.h _ (lp_equiv D w))
    (to_mp (twCls χ₁ Pa w) Pa.h _ (twist_lp χ₁ Pa w)) (to_mp (twCls χ₂ Pb w) Pb.h _ (twist_lp χ₂ Pb w))
    (stagesB _ _ _ _ _ _ (cls_list w hJ) h _ _ _)

end PositivityTheory.Rg.BcB.F.RS.JB

end
end

section
namespace PositivityTheory.Rg.BcB.F.RS

theorem join_module_holds : JoinMod := JB.joinMod_holds

theorem reading_module_holds : ReadMod := readMod_of join_module_holds

theorem reading_split_holds : ReadSplit := readSplit_of_join join_module_holds

end PositivityTheory.Rg.BcB.F.RS
end
