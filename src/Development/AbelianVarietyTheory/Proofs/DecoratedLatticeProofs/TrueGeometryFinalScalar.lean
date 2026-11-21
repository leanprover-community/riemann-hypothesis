import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterCongruenceInvarianceStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.SymChain.SymData.RowLam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sum_sum_lt {ι κ' : Type} [Fintype ι] [Fintype κ'] (f : ι → κ' → k)
    (hf : ∀ i j, valuation k (f i j) < 1) : valuation k (∑ i, ∑ j, f i j) < 1 := by
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hf i j)

theorem psi_inv_mul_eq_one (ψ : AddChar k Circle) (ϖ : kˣ) (hψ : GlobalTheory.SplitWeil.HasConductor ψ 1)
    (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {t : k} (ht : valuation k t < 1) :
    ψ (((ϖ⁻¹ : kˣ) : k) * t) = 1 := by
  have h1 := (hψ 1).2 (by simp)
  apply h1
  have hle : valuation k t ≤ valuation k (ϖ : k) := (hϖ t).1 ht
  rw [map_mul, map_one]
  calc valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k t
      ≤ valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k (ϖ : k) := by gcongr
    _ = 1 := by rw [← map_mul]; simp

end GlobalTheory.SymChain.SymData.RowLam

open GlobalTheory.SymChain.SymData.RowLam in
theorem GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  intro k _ _ _ _ s κ S x M hM hsup
  have hS := S.sym.2 x
  have hsimple : valuation k (GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k)) < 1 := by
    unfold GlobalTheory.RootEx.simpleSum
    apply val_sum_sum_lt
    intro i j
    split_ifs with h
    · exact hsup i j h
    · simp
  have hdiff : valuation k (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ -
      ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) < 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply val_sum_sum_lt
    intro a b
    split_ifs with h
    · simpa [Matrix.toBlocks₁₁] using hM a b
    · simp
  have e1 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hsimple
  have e2 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hdiff
  have e3 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁) =
      S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) := by
    rw [mul_sub, AddChar.map_sub_eq_div] at e2
    exact div_eq_one.mp e2
  rw [hS, e1, e3]
  simp
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  atlas_forward_decl GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiCol

theorem lam_eq_colLam : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (GlobalTheory.FamTraceChi.reductionYZero W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → (((a.G i).S.P.lam x : ℂˣ) : ℂ) = GlobalTheory.FamTraceChiCol.colLam (F0 W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i x hx
  obtain ⟨g, hg⟩ : ∃ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g :=
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.true_geometry_final_vector W hW u a ha hat row col hc κ hκ y hy hyU i x hx g hg
  rw [GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum (a.G i).S x _ h1 h2, GlobalTheory.T.true_geometry_final_volume W hW u a ha hat row col hc κ hκ y hy hyU i g hg]

end GlobalTheory.FamTraceChiCol

end
end
