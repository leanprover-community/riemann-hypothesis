import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

section
namespace PositivityTheory.Lit1.PTN

theorem nineAdd_intro {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    {f0 : A0 →ₗ[ZMod N] A1} {f1 : A1 →ₗ[ZMod N] A2} {f3 : A3 →ₗ[ZMod N] A4}
    {f4 : A4 →ₗ[ZMod N] A5} {f6 : A6 →ₗ[ZMod N] A7} {f7 : A7 →ₗ[ZMod N] A8}
    {B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : Type} [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4] [AddCommGroup B5] [AddCommGroup B6] [AddCommGroup B7] [AddCommGroup BetaSesquilinearity]
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ)
    (h0 : ∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) (h1 : ∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a))
    (h3 : ∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) (h4 : ∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a))
    (h6 : ∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) (h7 : ∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a))
    (i0 : Function.Injective g0) (x1 : Function.Exact g0 g1) (x2 : Function.Exact g1 g2)
    (x3 : Function.Exact g2 g3) (x4 : Function.Exact g3 g4) (x5 : Function.Exact g4 g5)
    (x6 : Function.Exact g5 g6) (x7 : Function.Exact g6 g7) (s7 : Function.Surjective g7) :
    NineAdd f0 f1 f3 f4 f6 f7 :=
  ⟨AddCommGrpCat.of B0, AddCommGrpCat.of B1, AddCommGrpCat.of B2, AddCommGrpCat.of B3,
    AddCommGrpCat.of B4, AddCommGrpCat.of B5, AddCommGrpCat.of B6, AddCommGrpCat.of B7,
    AddCommGrpCat.of BetaSesquilinearity, g0, g1, g2, g3, g4, g5, g6, g7, e0, e1, e2, e3, e4, e5, e6, e7, e8, ε,
    h0, h1, h3, h4, h6, h7, i0, x1, x2, x3, x4, x5, x6, x7, s7⟩

end PositivityTheory.Lit1.PTN
end

section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def reindexAdd {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β) :
    (∀ a, P (e a)) ≃+ (∀ b, P b) :=
  { Equiv.piCongrLeft P e with
    map_add' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.add_apply, Equiv.piCongrLeft_apply_apply] }

theorem reindexAdd_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) : reindexAdd P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

theorem reindexAdd_symm_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (g : ∀ b, P b) (a : α) : (reindexAdd P e).symm g a = g (e a) := by
  have h := reindexAdd_apply P e ((reindexAdd P e).symm g) a
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem ptLocalDualMap_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) (ξ : ∀ k, cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e ξ) y =
      ∑ k, ptLocalPairing φ D M inv (e k) h (ξ k) (ptRes φ (dualRep D M) (e k) s y) := by
  rw [ptLocalDualMap_apply]
  refine (Fintype.sum_equiv e _ _ (fun k => ?_)).symm
  rw [reindexAdd_apply]

theorem ptGlobalToLocal_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (r : ℕ) (x : cohomology M r) (k : κ) :
    (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm
      ((ptGlobalToLocal φ M r).hom x) k = ptRes φ M (e k) r x := by
  rw [reindexAdd_symm_apply, ptGlobalToLocal_apply]

theorem locSq_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (r : ℕ)
    {X : Type} [AddCommGroup X] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    (res : ∀ k, X →+ Xk k) (E : X ≃+ cohomology M r)
    (Ev : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : X) :
    (ptGlobalToLocal φ M r).hom (E x) =
      reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ev k (res k x)) := by
  apply (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  funext k
  rw [ptGlobalToLocal_reindex, sq]


def finsetCoeEquiv {α : Type} (S : Finset α) : S ≃ (S : Set α) where
  toFun v := ⟨v.1, Finset.mem_coe.2 v.2⟩
  invFun w := ⟨w.1, Finset.mem_coe.1 w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


end PositivityTheory.Lit1.PTN
end
end

section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in

theorem nineAdd_of_found2 {N : ℕ} [NeZero N]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type} [Fintype ι] {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
    {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (δ₁ : (cohomology (dualRep D M) 2 →+ QZ) →+ cohomology M 1)
    (δ₂ : (cohomology (dualRep D M) 1 →+ QZ) →+ cohomology M 2)
    (hx : Function.Injective (ptGlobalToLocal φ M 0).hom ∧
      Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁ ∧
      Function.Exact δ₁ (ptGlobalToLocal φ M 1).hom ∧
      Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂ ∧
      Function.Exact δ₂ (ptGlobalToLocal φ M 2).hom ∧
      Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) ∧
      Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)))

    {H0 H1 H2 : Type} [AddCommGroup H0] [Module (ZMod N) H0] [AddCommGroup H1] [Module (ZMod N) H1]
    [AddCommGroup H2] [Module (ZMod N) H2]
    {L0 L1 L2 : κ → Type} [∀ k, AddCommGroup (L0 k)] [∀ k, Module (ZMod N) (L0 k)]
    [∀ k, AddCommGroup (L1 k)] [∀ k, Module (ZMod N) (L1 k)]
    [∀ k, AddCommGroup (L2 k)] [∀ k, Module (ZMod N) (L2 k)]
    {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module (ZMod N) Y0] [AddCommGroup Y1] [Module (ZMod N) Y1]
    [AddCommGroup Y2] [Module (ZMod N) Y2]
    {W0 W1 W2 : κ → Type} [∀ k, AddCommGroup (W0 k)] [∀ k, Module (ZMod N) (W0 k)]
    [∀ k, AddCommGroup (W1 k)] [∀ k, Module (ZMod N) (W1 k)]
    [∀ k, AddCommGroup (W2 k)] [∀ k, Module (ZMod N) (W2 k)]
    (res0 : ∀ k, H0 →ₗ[ZMod N] L0 k) (res1 : ∀ k, H1 →ₗ[ZMod N] L1 k)
    (res2 : ∀ k, H2 →ₗ[ZMod N] L2 k)
    (rs0 : ∀ k, Y0 →ₗ[ZMod N] W0 k) (rs1 : ∀ k, Y1 →ₗ[ZMod N] W1 k) (rs2 : ∀ k, Y2 →ₗ[ZMod N] W2 k)
    (P0 : ∀ k, L0 k → W2 k → ZMod N) (P1 : ∀ k, L1 k → W1 k → ZMod N)
    (P2 : ∀ k, L2 k → W0 k → ZMod N)
    (f0 : H0 →ₗ[ZMod N] ∀ k, L0 k) (f1 : (∀ k, L0 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y2)
    (f3 : H1 →ₗ[ZMod N] ∀ k, L1 k) (f4 : (∀ k, L1 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y1)
    (f6 : H2 →ₗ[ZMod N] ∀ k, L2 k) (f7 : (∀ k, L2 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y0)
    (hf0 : ∀ x k, f0 x k = res0 k x) (hf3 : ∀ x k, f3 x k = res1 k x)
    (hf6 : ∀ x k, f6 x k = res2 k x)
    (hf1 : ∀ x y, f1 x y = ∑ k, P0 k (x k) (rs2 k y))
    (hf4 : ∀ x y, f4 x y = ∑ k, P1 k (x k) (rs1 k y))
    (hf7 : ∀ x y, f7 x y = ∑ k, P2 k (x k) (rs0 k y))

    (E0 : H0 ≃+ cohomology M 0) (E1 : H1 ≃+ cohomology M 1) (E2 : H2 ≃+ cohomology M 2)
    (Ev0 : ∀ k, L0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 0)
    (Ev1 : ∀ k, L1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 1)
    (Ev2 : ∀ k, L2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) 2)
    (F0 : Y0 ≃+ cohomology (dualRep D M) 0) (F1 : Y1 ≃+ cohomology (dualRep D M) 1)
    (F2 : Y2 ≃+ cohomology (dualRep D M) 2)
    (Fv0 : ∀ k, W0 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 0)
    (Fv1 : ∀ k, W1 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 1)
    (Fv2 : ∀ k, W2 k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) 2)
    (sq0 : ∀ k x, Ev0 k (res0 k x) = ptRes φ M (e k) 0 (E0 x))
    (sq1 : ∀ k x, Ev1 k (res1 k x) = ptRes φ M (e k) 1 (E1 x))
    (sq2 : ∀ k x, Ev2 k (res2 k x) = ptRes φ M (e k) 2 (E2 x))
    (tq0 : ∀ k y, Fv0 k (rs0 k y) = ptRes φ (dualRep D M) (e k) 0 (F0 y))
    (tq1 : ∀ k y, Fv1 k (rs1 k y) = ptRes φ (dualRep D M) (e k) 1 (F1 y))
    (tq2 : ∀ k y, Fv2 k (rs2 k y) = ptRes φ (dualRep D M) (e k) 2 (F2 y))
    (hQ0 : ∀ k a b, zmodToQZ N (P0 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 0 + 2 = 2) (Ev0 k a) (Fv2 k b)))
    (hQ1 : ∀ k a b, zmodToQZ N (P1 k a b) =
      inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 1 + 1 = 2) (Ev1 k a) (Fv1 k b)))
    (hQ2 : ∀ k a b, zmodToQZ N (P2 k a b) =
      - inv (e k) (cupPairing (ptLocalEval φ D M (e k)) (rfl : 2 + 0 = 2) (Ev2 k a) (Fv0 k b))) :
    NineAdd f0 f1 f3 f4 f6 f7 := by
  obtain ⟨i0, x1, x2, x3, x4, x5, x6, x7, s7⟩ := hx
  have hL : ∀ {r : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod N) H] {L : κ → Type}
      [∀ k, AddCommGroup (L k)] [∀ k, Module (ZMod N) (L k)] (res : ∀ k, H →ₗ[ZMod N] L k)
      (f : H →ₗ[ZMod N] ∀ k, L k) (hf : ∀ x k, f x k = res k x) (E : H ≃+ cohomology M r)
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : H),
      (ptGlobalToLocal φ M r).hom (E x) =
        ((1 : ℤˣ) : ℤ) • ((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) (f x) := by
    intro r H _ _ L _ _ res f hf E Ev sq x
    rw [Units.val_one, one_smul]
    rw [locSq_reindex φ e M r (fun k => (res k).toAddMonoidHom) E Ev sq x]
    rw [AddEquiv.trans_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [AddEquiv.piCongrRight_apply, hf]
    rfl
  have hT : ∀ {r s : ℕ} (h : r + s = 2) {L : κ → Type} [∀ k, AddCommGroup (L k)]
      [∀ k, Module (ZMod N) (L k)] {Y : Type} [AddCommGroup Y] [Module (ZMod N) Y]
      {W : κ → Type} [∀ k, AddCommGroup (W k)] [∀ k, Module (ZMod N) (W k)]
      (rs : ∀ k, Y →ₗ[ZMod N] W k) (P : ∀ k, L k → W k → ZMod N)
      (f : (∀ k, L k) →ₗ[ZMod N] Module.Dual (ZMod N) Y)
      (hf : ∀ x y, f x y = ∑ k, P k (x k) (rs k y))
      (Ev : ∀ k, L k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
      (F : Y ≃+ cohomology (dualRep D M) s)
      (Fv : ∀ k, W k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) s)
      (tq : ∀ k y, Fv k (rs k y) = ptRes φ (dualRep D M) (e k) s (F y)) (ε : ℤˣ)
      (hQ : ∀ k a b, (ε : ℤ) • zmodToQZ N (P k a b) =
        inv (e k) (cupPairing (ptLocalEval φ D M (e k)) h (Ev k a) (Fv k b))) (x : ∀ k, L k),
      ptLocalDualMap φ D M inv h (((AddEquiv.piCongrRight Ev).trans
          (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e)) x) =
        (ε : ℤ) • dualQZ F (f x) := by
    intro r s h L _ _ Y _ _ W _ _ rs P f hf Ev F Fv tq ε hQ x
    refine AddMonoidHom.ext fun y => ?_
    rw [AddEquiv.trans_apply]
    change ptLocalDualMap φ D M inv h (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e
      (fun k => Ev k (x k))) y = _
    rw [ptLocalDualMap_reindex, AddMonoidHom.smul_apply, dualQZ_apply, hf, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hQ, tq, AddEquiv.apply_symm_apply, ptLocalPairing_apply]
  exact nineAdd_intro (ptGlobalToLocal φ M 0).hom.toAddMonoidHom
    (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁
    (ptGlobalToLocal φ M 1).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂
    (ptGlobalToLocal φ M 2).hom.toAddMonoidHom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl))
    E0 ((AddEquiv.piCongrRight Ev0).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 0) e)) (dualQZ F2)
    E1 ((AddEquiv.piCongrRight Ev1).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 1) e)) (dualQZ F1)
    E2 ((AddEquiv.piCongrRight Ev2).trans
      (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) 2) e)) (dualQZ F0)
    ![1, -1, 1, 1, 1, -1]
    (hL res0 f0 hf0 E0 Ev0 sq0) (hT _ rs2 P0 f1 hf1 Ev0 F2 Fv2 tq2 (-1) (fun k a b => by rw [hQ0, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    (hL res1 f3 hf3 E1 Ev1 sq1) (hT _ rs1 P1 f4 hf4 Ev1 F1 Fv1 tq1 1 (fun k a b => by rw [hQ1, Units.val_one, one_smul]))
    (hL res2 f6 hf6 E2 Ev2 sq2) (hT _ rs0 P2 f7 hf7 Ev2 F0 Fv0 tq0 (-1) (fun k a b => by rw [hQ2, Units.val_neg, Units.val_one, neg_one_zsmul, neg_neg]))
    i0 x1 x2 x3 x4 x5 x6 x7 s7

end PositivityTheory.Lit1.PTN
end
end
