import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

theorem exists_finG_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram →
    ∃ g : GfC V, finG V g = M := by
  intro D V M hM
  obtain ⟨g0, hg0⟩ := GlobalTheory.FunObj.UA_le_range_finE V hM
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g0) (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g0)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  rw [← hg0]
  change Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g0)
  rw [k2]

end GlobalTheory.FrameTransport

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram → ∃ g : GfC V, finG V g = M := by
  atlas_forward_decl GlobalTheory.FrameTransport.exists_finG_eq
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  atlas_forward_decl GlobalTheory.FrameTransport.frConj_mem_UA
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toAfE_inc (D : D7) (x : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
  have h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])
  have h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])
  show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _
  rw [h2, ← h1, RingEquiv.symm_apply_apply]

theorem adSwap_inc (D : D7) (x : D.host.E) : adSwap D (StandardLatticesGL3.inc D x) = inclEAf D x := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _
  rw [toAfE_inc]
  rfl

theorem finE_val_of_isRat {D : D7} {V : HSp D} {g : GA D V} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : GlobalTheory.RatAut.IsRat V g a) :
    (Lev.finE V g).val = a.map (inclEAf D) := by
  have e : (Lev.finE V g).val =
      (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y)) := rfl
  rw [e, show Formalism.L2.Theta.mt V g = _ from h]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rfl

theorem frConj_ratG : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E),
    Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 →
    ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  intro D V fr hfr
  let S : Subgroup (StandardLatticesGL3.GA D V.rank) :=
    ((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
  suffices hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by
    intro γ hγ
    obtain ⟨q, hq, e⟩ := hS hγ
    exact ⟨q, hq, e⟩
  rw [GlobalTheory.NormSum.ratG, Subgroup.closure_le]
  rintro g ⟨γ₀, hγ₀⟩

  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := g.2
  have hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose := by
    ext i j
    simp [StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]
  have hu : (γ₀.map D.host.conj).transpose * γ₀ = 1 := by
    apply Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
    exact hg.trans h1.symm
  have hu' : γ₀ᴴ * γ₀ = 1 := by
    have : γ₀ᴴ = (γ₀.map D.host.conj).transpose := Matrix.ext fun i j => by
      show star (γ₀ j i) = D.host.conj (γ₀ j i)
      exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)
    rw [this, hu]

  set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF
  set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi
  have hFFi : F * Fi = 1 := by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Fᴴ * V.gram * F = 1 := hfr
  have hJ : V.gram = Fiᴴ * Fi := by
    have := congrArg (fun M => Fiᴴ * M * Fi) hfr'
    simp only [Matrix.mul_one] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
  set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha
  have hau : aᴴ * V.gram * a = V.gram := by
    have e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi := by
      rw [ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]
  obtain ⟨g', hg'Q, hg'⟩ := GlobalTheory.RatAut.exists_of_unitary V hau
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')
  have hkC : k ∈ GfC V := MonoidHom.mem_ker.2 k1
  have hfin : finG V ⟨k, hkC⟩ = Lev.finE V g' := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')
    rw [k2]
  refine ⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩
  show finG V ⟨k, hkC⟩ = frConj fr g.1
  rw [hfin, frConj_apply]
  apply Units.ext
  rw [finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]
  have eb : ∀ (M : GL (Fin V.rank) D.host.E),
      (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D) := fun M => rfl
  have eg : (Formalism.UG.bc (adSwap D) g.1).val =
      γ₀.map (inclEAf D) := by
    show g.1.val.map (adSwap D) = _
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, Matrix.map_map]
    exact Matrix.ext fun i j => adSwap_inc D (γ₀ i j)
  rw [eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]

end GlobalTheory.FrameTransport
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardRational_mem_unitaryRational : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  atlas_forward_decl GlobalTheory.FrameTransport.frConj_ratG
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameTransport.IntSwap

theorem toFinE_mem_intAd {D : D7} {x : StandardLatticesGL3.AE D} (hx : x ∈ StandardLatticesGL3.OhE D) :
    GlobalTheory.BotFormula.toFinE D x ∈ Formalism.UG.intAd D.host.E := by
  have key : ∀ y : StandardLatticesGL3.AE D,
      (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)) y ∈
        AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ℚ ⊗[ℚ] D.host.E |
          ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf ℚ, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[ℚ] (o : D.host.E)} →
      GlobalTheory.BotFormula.toFinE D y ∈ Formalism.UG.intAd D.host.E := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).1 hy
  have hle : StandardLatticesGL3.OhE D ≤ (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      refine key _ (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, rfl⟩)
      exact (one_mem (v.adicCompletionIntegers ℚ) : _)
    · refine key _ (AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, ?_⟩)
      rfl
  exact hle hx

theorem swapAE_mem_intAf {D : D7} {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)}) :
    Lev.swapAE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hle : AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup.comap (Lev.swapAE D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, o, rfl⟩
    have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) *
          ((1 : D.host.E) ⊗ₜ[D.host.F] (a : Formalism.L2.Herm.Af D.host.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    show Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
    rw [e]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(o : D.host.E), o, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  exact hle hy

end GlobalTheory.FrameTransport.IntSwap

theorem GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D →
    GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D x hx
  have h1 := GlobalTheory.FrameTransport.IntSwap.toFinE_mem_intAd hx
  have h2 : GlobalTheory.BotFormula.toAfE D x ∈ AddSubgroup.closure
      {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
        ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} := by
    refine (GlobalTheory.LFun.mem_int_iff _).2 fun P => ?_
    have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.BotFormula.toAfE D x) = GlobalTheory.BotFormula.toFinE D x :=
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _
    rw [e]
    exact h1 P
  exact GlobalTheory.FrameTransport.IntSwap.swapAE_mem_intAf h2
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D → GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  atlas_forward_decl GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameTransport

theorem colLat_inv_mulVec_int {K : Type} [Field K] [NumberField K] {n : ℕ} (fr : GL (Fin n) K)
    (x : Fin n → K) (hx : x ∈ colLat fr) : ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K := by
  let M : Submodule (𝓞 K) (Fin n → K) :=
    { carrier := {x | ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : fr⁻¹.val *ᵥ (c • a) = (algebraMap (𝓞 K) K c) • (fr⁻¹.val *ᵥ a) := by
          rw [← Matrix.mulVec_smul, algebraMap_smul]
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem ⟨c, rfl⟩ (ha i) }
  have hle : colLat fr ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ i
    have hcol : (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j) = fr.val *ᵥ Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    show (fr⁻¹.val *ᵥ (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j)) i ∈ _
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  exact hle hx

theorem inclEAf_intOE_mem {D : D7} (e : D.host.E) (he : e ∈ Formalism.UG.intOE D.host.E) :
    inclEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem hatL_colLat_coord_int {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    ∀ i, ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  let S := Formalism.L2.Herm.intAf D.host.F D.host.E
  let P : Matrix (Fin n) (Fin n) (Lev.EAf D) := (Formalism.UG.bc (inclEAf D) fr)⁻¹.val
  have hP : P = (fr⁻¹.val).map (inclEAf D) := rfl
  let M : Submodule S (Fin n → Lev.EAf D) :=
    { carrier := {y | ∀ i, (P *ᵥ y) i ∈ S}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : P *ᵥ (c • a) = (c : Lev.EAf D) • (P *ᵥ a) := by
          rw [← Matrix.mulVec_smul]; rfl
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem c.2 (ha i) }
  have hle : Submodule.span S ((fun x : Fin n → D.host.E => fun i =>
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) '' (colLat fr : Set (Fin n → D.host.E))) ≤ M := by
    refine (Submodule.span_le (p := M)).2 ?_
    rintro _ ⟨x, hx, rfl⟩ i
    have h1 := colLat_inv_mulVec_int fr x hx i
    have h2 : (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i =
        inclEAf D ((fr⁻¹.val *ᵥ x) i) := by
      rw [hP, RingHom.map_mulVec]; rfl
    show (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i ∈ S
    rw [h2]
    exact inclEAf_intOE_mem _ h1
  exact hle hy

end GlobalTheory.FrameTransport

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  atlas_forward_decl GlobalTheory.FrameTransport.hatL_colLat_coord_int
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  atlas_forward_decl GlobalTheory.FrameColSmul.mulVec_mem
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HatIdealCarry

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def intOf (b : 𝓞 E) : Formalism.L2.Herm.intAf F E :=
  ⟨Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b),
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)⟩

theorem incl_smul (b : 𝓞 E) (l : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((b • l) i)) =
      intOf (F := F) b • (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
  funext i
  show _ = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b) *
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)
  rw [← map_mul, Pi.smul_apply, Algebra.smul_def]

theorem incl_add (a b : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a + b) i)) =
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (a i)) +
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (b i)) := by
  funext i
  exact map_add _ (a i) (b i)

theorem mulVec_intSmul (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (r : Formalism.L2.Herm.intAf F E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    M *ᵥ (r • v) = r • (M *ᵥ v) := by
  have e : r • v = (r : E ⊗[F] Formalism.L2.Herm.Af F) • v := rfl
  have e' : r • (M *ᵥ v) = (r : E ⊗[F] Formalism.L2.Herm.Af F) • (M *ᵥ v) := rfl
  rw [e, e', Matrix.mulVec_smul]

theorem intOf_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) {b : 𝓞 E} (hb : b ∈ 𝔪) (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  refine Submodule.span_induction
    (p := fun z _ => intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨b • x, Submodule.smul_mem_smul hb hx, ?_⟩
    exact incl_smul b x
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [smul_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem transportGen (uf : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L Λ : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := F) L → uf *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (𝔪 : Ideal (𝓞 E)) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • L)) : uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  have gen : ∀ w ∈ 𝔪 • L, uf *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (w i)) ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro b hb l hl
      rw [incl_smul b l, mulVec_intSmul]
      exact intOf_smul_mem Λ 𝔪 hb _ (hL _ (Submodule.subset_span ⟨l, hl, rfl⟩))
    · intro a c ha hc
      rw [incl_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ ha hc
  refine Submodule.span_induction
    (p := fun y _ => uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨w, hw, rfl⟩
    exact gen w hw
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [mulVec_intSmul]; exact Submodule.smul_mem _ c ha

end Gen

theorem transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  fun uf L Λ hL 𝔪 y hy => transportGen uf.val L Λ hL 𝔪 y hy

end GlobalTheory.HatIdealCarry
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLatticeMap_idealMul_transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  atlas_forward_decl GlobalTheory.HatIdealCarry.transport
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.FrameTransport.Cong

variable {D : D7}

theorem adSwap_mem_intAf (x : StandardLatticesGL3.AE D) (hx : x ∈ StandardLatticesGL3.OhE D) :
    adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE x hx

theorem adSwap_inc (e : D.host.E) : adSwap D (StandardLatticesGL3.inc D e) = inclEAf D e := by
  have h1 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ e) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  have h2 : GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e := by
    show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e)) = _
    rw [h1, RingEquiv.symm_apply_eq]
    show _ = GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e)
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e)) = _
  rw [h2]
  rfl

theorem intG_entries {n : ℕ} (k : StandardLatticesGL3.GA D n) (hk : k ∈ GlobalTheory.NormSum.intG D n) : StandardLatticesGL3.IntG D k.1 := by
  have hmul : ∀ a b : GL (Fin n) (StandardLatticesGL3.AE D), (∀ i j, a.val i j ∈ StandardLatticesGL3.OhE D) → (∀ i j, b.val i j ∈ StandardLatticesGL3.OhE D) →
      ∀ i j, (a * b).val i j ∈ StandardLatticesGL3.OhE D := fun a b ha hb i j => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hb l j)
  let H : Subgroup (StandardLatticesGL3.GA D n) :=
    { carrier := {k | StandardLatticesGL3.IntG D k.1}
      mul_mem' := fun {a b} ha hb i j => by
        refine ⟨hmul a.1 b.1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j, ?_⟩
        have e : ((a * b : StandardLatticesGL3.GA D n) : GL (Fin n) (StandardLatticesGL3.AE D))⁻¹ = b.1⁻¹ * a.1⁻¹ := by
          rw [Subgroup.coe_mul, _root_.mul_inv_rev]
        rw [e]
        exact hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
      one_mem' := fun i j => by
        have h1 : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) i j ∈ StandardLatticesGL3.OhE D := fun i j => by
          rw [Matrix.one_apply]
          split_ifs
          exacts [Subring.one_mem _, Subring.zero_mem _]
        exact ⟨h1 i j, by rw [Subgroup.coe_one, inv_one]; exact h1 i j⟩
      inv_mem' := fun {a} ha i j => by
        refine ⟨(ha i j).2, ?_⟩
        rw [Subgroup.coe_inv, inv_inv]
        exact (ha i j).1 }
  exact (Subgroup.closure_le H).2 (fun k hk => hk) hk

theorem hatL_colLat_int {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (i : Fin n) :
    ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.completedColumnLattice_integral_frameCoords fr y hy i

theorem col_mem_hatL {n : ℕ} (fr : GL (Fin n) D.host.E) (j : Fin n) :
    (fun i => inclEAf D (fr.val i j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) :=
  Submodule.subset_span ⟨fun a => fr.val a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem eaf_mul_comm (a b : Lev.EAf D) : a * b = b * a := mul_comm a b

set_option maxHeartbeats 1000000 in
theorem hatL_colLat_of_int {n : ℕ} (fr : GL (Fin n) D.host.E) (z : Fin n → Lev.EAf D)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  have e : (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z =
      ∑ j, (⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j)) := by
    funext i
    rw [Finset.sum_apply]
    show ∑ j, (Formalism.UG.bc (inclEAf D) fr).val i j * z j =
      ∑ j, ((⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j))) i
    exact Finset.sum_congr rfl fun j _ => eaf_mul_comm _ _
  exact (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) e).mpr
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (col_mem_hatL fr j))

theorem mul_mem_spanIncl (𝔪 : Ideal (𝓞 D.host.E)) (a z : Lev.EAf D)
    (ha : a ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))))
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    a * z ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have h3 := Submodule.smul_mem _ (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha
  have e : (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • a = a * z := mul_comm z a
  exact e ▸ h3

theorem adSwap_hatId (𝔪 : Ideal (𝓞 D.host.E)) (c : StandardLatticesGL3.AE D) (hc : c ∈ SqNum.hatId D 𝔪) :
    adSwap D c ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have hle : SqNum.hatId D 𝔪 ≤ (Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))).toAddSubgroup.comap
        (adSwap D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have e : adSwap D (StandardLatticesGL3.inc D (b : D.host.E) * s) = inclEAf D (b : D.host.E) * adSwap D s :=
      (map_mul (adSwap D) _ _).trans (congrArg (· * adSwap D s) (adSwap_inc _))
    exact (congrArg (fun v => v ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) e).mpr
      (mul_mem_spanIncl 𝔪 _ _ (Submodule.subset_span ⟨b, hb, rfl⟩) (adSwap_mem_intAf s hs))
  exact hle hc

theorem hatL_smul_colLat {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D)
    (hw : ∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) :=
  GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice fr 𝔪 w hw

theorem hatL_transport {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D) (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L)) :
    uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  GlobalTheory.T.completedLatticeMap_idealMul_transport uf L Λ h 𝔪 y hy

theorem frConj_val {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ ((Formalism.UG.bc (adSwap D) k).val *ᵥ
      ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [frConj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem bc_adSwap_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    (Formalism.UG.bc (adSwap D) k).val i j = adSwap D (k.val i j) := rfl

theorem GL_mulVec_inv {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P.val *ᵥ (P⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem GL_inv_mulVec {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P⁻¹.val *ᵥ (P.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem frConj_sub {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y - y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ
      (((Formalism.UG.bc (adSwap D) k).val - 1) *ᵥ ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, GL_mulVec_inv (Formalism.UG.bc (inclEAf D) fr) y,
    frConj_val fr k y]

theorem bc_adSwap_sub_one_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    ((Formalism.UG.bc (adSwap D) k).val - 1) i j = adSwap D ((k.val - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [(map_one (adSwap D)).symm, (map_zero (adSwap D)).symm]

theorem frConj_stab {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, k.val i j ∈ StandardLatticesGL3.OhE D) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  rw [frConj_val]
  refine hatL_colLat_of_int fr _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (by rw [bc_adSwap_apply]; exact adSwap_mem_intAf _ (hk i j))
    (hatL_colLat_int fr y hy j)

theorem frConj_stab_iff {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : StandardLatticesGL3.IntG D k) (y : Fin n → Lev.EAf D) :
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  refine ⟨frConj_stab fr k (fun i j => (hk i j).1) y, fun h => ?_⟩
  have h2 := frConj_stab fr k⁻¹ (fun i j => (hk i j).2) _ h
  have e : (frConj fr k⁻¹).val *ᵥ ((frConj fr k).val *ᵥ y) = y := by
    rw [map_inv]; exact GL_inv_mulVec _ y
  exact e ▸ h2

theorem frConj_cong {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, (k.val - 1) i j ∈ SqNum.hatId D 𝔪) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  rw [frConj_sub fr k y]
  refine hatL_smul_colLat fr 𝔪 _ fun i => ?_
  show (∑ j, ((Formalism.UG.bc (adSwap D) k).val - 1) i j * ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) j) ∈ _
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 := mul_mem_spanIncl 𝔪 _ _ (adSwap_hatId 𝔪 _ (hk i j)) (hatL_colLat_int fr y hy j)
  rw [bc_adSwap_sub_one_apply k i j]
  exact h4

set_option maxHeartbeats 1000000 in

theorem conj_mem_congLev : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V fr uf Λ hL 𝔪 k hk hc hU
  have hM : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      uf⁻¹.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := fun x =>
    ((hL (uf⁻¹.val *ᵥ x)).trans (by rw [GL_mulVec_inv uf x])).symm
  have hg : ∀ x, (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x = uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg' : ∀ x, uf⁻¹.val *ᵥ ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x) = (frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) := by
    intro x
    rw [hg x, GL_inv_mulVec]
  refine ⟨hU, fun x => ?_, fun x hx => ?_⟩
  · refine (hM x).trans ((frConj_stab_iff fr k.1 (intG_entries k hk) _).trans ?_)
    exact ((hM ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x)).trans
      (Iff.of_eq (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (hg' x)))).symm
  · have hy := (hM x).1 hx
    have h5 := hatL_transport uf (colLat fr) Λ (fun v hv => (hL v).1 hv) 𝔪 _ (frConj_cong fr 𝔪 k.1 hc _ hy)
    have e : uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) - uf⁻¹.val *ᵥ x) =
        (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x - x := by
      exact (Matrix.mulVec_sub uf.val _ _).trans (congrArg₂ HSub.hSub (hg x).symm (GL_mulVec_inv uf x))
    exact Eq.mp (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) e) h5

end GlobalTheory.FrameTransport.Cong
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  atlas_forward_decl GlobalTheory.FrameTransport.Cong.conj_mem_congLev
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport.Onto

open scoped TensorProduct

theorem swapAE_sigR (D : D7) (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    Lev.swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Lev.swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]
  | tmul a e => rfl

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  exact swapAE_sigR D _

def adSwapEquiv (D : D7) : StandardLatticesGL3.AE D ≃+* Lev.EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem adSwapEquiv_apply (D : D7) (y : StandardLatticesGL3.AE D) : adSwapEquiv D y = adSwap D y := rfl

theorem sigR_inclEAf (D : D7) (e : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D e) = inclEAf D (D.sp.cm.sig e) := rfl

end GlobalTheory.FrameTransport.Onto

namespace GlobalTheory.FrameTransport.Onto

theorem cT_map_inclEAf (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) :
    (Formalism.UG.cT (↑D.sp.cm.sig) A).map (inclEAf D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (inclEAf D)) := by
  ext i j
  exact (sigR_inclEAf D (A j i)).symm

theorem cT_map_adSwap (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) :
    (Formalism.UG.cT (StandardLatticesGL3.sgA D) A).map (adSwap D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (adSwap D)) := by
  ext i j
  exact adSwap_sgA D (A j i)

theorem conj_unitary {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J P Pi M : Matrix (Fin n) (Fin n) R)
    (hPPi : P * Pi = 1) (hP : Formalism.UG.cT s P * J * P = 1) (hM : Formalism.UG.cT s M * J * M = J) :
    Formalism.UG.cT s (Pi * M * P) * (Pi * M * P) = 1 := by
  have h2 : Formalism.UG.cT s Pi * Formalism.UG.cT s P = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hJ : J = Formalism.UG.cT s Pi * Pi := by
    calc J = (Formalism.UG.cT s Pi * Formalism.UG.cT s P) * J * (P * Pi) := by rw [h2, hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Pi * (Formalism.UG.cT s P * J * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← hP]
  calc _ = Formalism.UG.cT s P * (Formalism.UG.cT s M * (Formalism.UG.cT s Pi * Pi) * M) * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hM]

theorem _root_.GlobalTheory.FrameTransport.exists_frConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  intro D V fr hfr M hM
  let P : GL (Fin V.rank) (Lev.EAf D) := Formalism.UG.bc (inclEAf D) fr
  let N : GL (Fin V.rank) (Lev.EAf D) := P⁻¹ * M * P
  let h0 : GL (Fin V.rank) (StandardLatticesGL3.AE D) := Formalism.UG.bc (adSwapEquiv D).symm.toRingHom N
  have hbc : Formalism.UG.bc (adSwap D) h0 = N := by
    ext i j
    show adSwap D ((adSwapEquiv D).symm _) = _
    rw [← adSwapEquiv_apply, RingEquiv.apply_symm_apply]
  have hbcm : h0.val.map (adSwap D) = N.val := congrArg Units.val hbc
  have hPPi : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) P.val * V.gram.map (inclEAf D) * P.val = 1 := by
    have := congrArg (fun X => X.map (inclEAf D)) hfr
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_map_inclEAf] at this
    exact this
  have hN : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) N.val * N.val = 1 := by
    have hNv : N.val = (P⁻¹).val * M.val * P.val := by simp only [N, Units.val_mul]
    rw [hNv]
    exact conj_unitary _ _ _ _ _ hPPi hfr' hM
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · show Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        h0.val = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    apply Matrix.map_injective (adSwapEquiv D).injective
    change (Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val * h0.val).map (adSwap D) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (adSwap D)
    rw [Matrix.map_mul, cT_map_adSwap, hbcm, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  · show frConj fr h0 = M
    rw [frConj_apply, hbc]
    show P * (P⁻¹ * M * P) * P⁻¹ = M
    group

end GlobalTheory.FrameTransport.Onto
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnitary_frameConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  atlas_forward_decl GlobalTheory.FrameTransport.exists_frConj_eq
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

open GlobalTheory.FrameTransport in

theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' _ _ p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (DoubleCoset.eq _ _ _ _).1
    (DoubleCoset.out_eq' (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank)
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (DoubleCoset.eq _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  atlas_forward_decl GlobalTheory.FrameTransport.finCl_card_le
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 2000000 in

theorem finCl_mk_eq_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (a b : GfC V) :
    DoubleCoset.mk (ratFin V) (K.comap (finG V)) a = DoubleCoset.mk (ratFin V) (K.comap (finG V)) b ↔
      (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V a.1) :
        Cl D.sp.cm V.gram K) = DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V b.1) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    have hγ' : finG V γ ∈ (GQ V).map (Lev.finE V) := hγ
    obtain ⟨γ0, hγ0, e0⟩ := hγ'
    refine ⟨GlobalTheory.DefFree.finU V γ.1, ?_, GlobalTheory.DefFree.finU V k.1, ?_, ?_⟩
    · have : GlobalTheory.DefFree.finU V γ.1 = GlobalTheory.DefFree.finU V γ0 := Subtype.ext e0.symm
      rw [this]
      exact GlobalTheory.DefFree.AdelCls.rat_mem V γ0 hγ0
    · exact Subgroup.mem_subgroupOf.2 hk
    · simp only [Subgroup.coe_mul, map_mul]
  · rintro ⟨q, hq, k, hk, e⟩
    have hq' : q ∈ (GQ V).map (GlobalTheory.DefFree.finU V) := by rw [GlobalTheory.DefFree.AdelCls.map_rat]; exact hq
    obtain ⟨γ0, hγ0, rfl⟩ := hq'
    obtain ⟨γ1, hγ1, e1⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V (GlobalTheory.DefFree.finU V γ0)
    obtain ⟨κ, hκ, e2⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V k
    refine ⟨⟨γ1, hγ1⟩, ?_, ⟨κ, hκ⟩, ?_, ?_⟩
    · refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨γ0, hγ0, ?_⟩)
      exact (congrArg Subtype.val e1).symm
    · refine Subgroup.mem_comap.2 ?_
      have := Subgroup.mem_subgroupOf.1 hk
      rw [← e2] at this
      exact this
    · apply Subtype.ext
      have hx : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GinfC V := by
        rw [← GlobalTheory.DefFree.AdelCls.finU_eq_one_iff, MonoidHom.map_mul, MonoidHom.map_inv, MonoidHom.map_mul, MonoidHom.map_mul,
          e1, e2, e]
        exact inv_mul_cancel _
      have hy : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).inv_mem b.2) ((GfC V).mul_mem ((GfC V).mul_mem hγ1 a.2) hκ)
      exact inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hy hx)

theorem card_finCl_eq (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    Nat.card (FinCl V K) = Nat.card (Cl D.sp.cm V.gram K) := by
  let f : FinCl V K → Cl D.sp.cm V.gram K := Quotient.lift
    (fun x : GfC V => (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V x.1) :
      Cl D.sp.cm V.gram K))
    (fun a b h => (finCl_mk_eq_iff V K a b).1 ((DoubleCoset.eq'' _ _).2 h))
  refine Nat.card_eq_of_bijective f ⟨fun c c' h => ?_, fun c => ?_⟩
  · induction c using Quotient.inductionOn with | h a => ?_
    induction c' using Quotient.inductionOn with | h b => ?_
    exact (finCl_mk_eq_iff V K a b).2 h
  · induction c using Quotient.inductionOn with | h x => ?_
    obtain ⟨h, hh, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V x
    exact ⟨DoubleCoset.mk _ _ (⟨h, hh⟩ : GfC V), by
      show (DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V h) : Cl D.sp.cm V.gram K) = _
      rw [e]⟩

theorem card_clPlus_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U →
    (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  intro D T L sc G U hS
  have h := GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence G hS (.top 0) (Nat.zero_le _) G.modul (G.pl.modul_ne_bot sc) G.Kplus le_rfl
  rw [card_finCl_eq] at h
  exact h

end GlobalTheory.ClassCount

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  atlas_forward_decl GlobalTheory.ClassCount.card_clPlus_le
end
