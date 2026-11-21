import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeConventionOfHermitian
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.LocalToGlobal.Columns.TiedValRat

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.MainNotions.GlobalTheoryTheory.Inhab

def ColTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) : Prop :=
  Nonempty ((D.mem u).C.cls 0) ∧
  (∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)) ∧
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (nfAll ((D.fm u).lam 0)
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colTie_of_colTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTieW B) : ColTie B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w γ hγ x => ?_, hinf⟩
  obtain ⟨γ0, hγ0, hx⟩ := hloc w
  rw [hx]
  exact forall_congr' fun c => mem_iff_of_locBasis D w ((D.fm u).lam 0) (B.Q c) (B.eQ c) (γ0 c) (γ c)
    (hγ0 c) (hγ c) (co x c)

theorem colTieW_of {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTie B) : ColTieW B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w => ?_, hinf⟩
  have hex : ∀ c τ, ∃ g, LocBasis D w (B.Q c τ) (B.eQ c τ) g := fun c τ =>
    Formalism.L2.GlobalTheoryTheory.TraceIntegrality.exists_locBasis w (B.Q c τ) (B.Q_good c τ) (B.eQ c τ)
  choose γ hγ using hex
  exact ⟨γ, hγ, hloc w γ hγ⟩

theorem colTieW_iff {D : D7} {u : D.what₂.Word} (B : ColBase D u) : ColTieW B ↔ ColTie B :=
  ⟨colTie_of_colTieW B, colTieW_of B⟩

theorem column_value_nonempty_iff (D : D7) (u : D.what₂.Word) :
    Nonempty (ColVal D u) ↔ ∃ B : ColBase D u, ColTieW B := by
  rw [ColVal_nonempty_iff]
  exact exists_congr fun B => (colTieW_iff B).symm

theorem column_value_of_tie_local_bases
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → adm3 D → ∀ u : D.what₂.Word, ∃ B : ColBase D u, ColTieW B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  intro D h1 h2 u
  exact (column_value_nonempty_iff D u).mpr (h D h1 h2 u)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def K0 (D : D7) : Coord D.sp.cm (D.sp.X 0) (Fin D.R.k) := ⟨D.sp.crd0, D.sp.gram0, D.sp.hermitianForm_base_coordinates⟩




theorem dualSub_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    flipTwoThree.dualSub S L = (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup := by
  ext x
  show (∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range) ↔ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  simp only [Submodule.mem_one, RingHom.mem_range]

theorem card_ringOfIntegers_quot_natCast_eq_pow (D : D7) (T : ℕ) :
    Nat.card (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) = T ^ (2 * D.R.f) := by
  have h1 := Ideal.absNorm_span_singleton (((T : ℕ) : 𝓞 D.host.E))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  rw [h1]
  have h2 : ((T : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (T : ℤ) := by simp
  rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank, Formalism.MainNotions.StandardLattice.finrank_host D]
  simp [Int.natAbs_pow]


end Formalism.L2.GlobalTheoryTheory

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_lattice_eq_global {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    (K0 D).lat (D.clsLat u 0 c) = globLat ((Lv u).y c).1 (Lv u).Lb :=
  eq_glob_of_hat ((K0 D).isLat_lat (D.clsLat_lat u 0 c)) _ (fun v => by exact (Lv u).y_lat c v)

theorem Lb_le_dl_lv {D : D7} (Lv : LevelData D) (u : D.what₂.Word) :
    (Lv u).Lb ≤ dl D.sp.cm.sig (K0 D).J (Lv u).Lb := by
  intro x hx
  exact Submodule.subset_span ((Lv u).Lb_int x hx)

theorem class_lattice_integral {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    D.clsLat u 0 c ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c) := by
  have h1 : (K0 D).lat (D.clsLat u 0 c) ≤ (K0 D).lat (Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c)) := by
    rw [(K0 D).lat_dual, class_lattice_eq_global Lv u c]
    exact le_trans (glob_mono _ (Lb_le_dl_lv Lv u)) (glob_dl_le _ _ _ _ (by exact ((Lv u).y c).2))
  intro x hx
  have h2 := h1 ⟨x, hx, rfl⟩
  rw [(K0 D).mem_lat] at h2
  simpa using h2

theorem latT_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    flipTwoThree.LatT (D.sp.X 0) (flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dualSub_eq]
    exact class_lattice_integral F.herm.base.lev0 u c hx
  · obtain ⟨e⟩ := (F.herm.atT u).disc 0 (Nat.zero_le _) c
    rw [dualSub_eq, AddSubgroup.relIndex, ← card_ringOfIntegers_quot_natCast_eq_pow D (flipTwoThree.Tu D u)]
    have := Nat.card_congr e.toEquiv
    have hT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [hT, ← this]
    rfl

theorem classes_level_zero_nonempty {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (F.herm.base.lev0 u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

def ColRest {D : D7} {u : D.what₂.Word} (B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u) : Prop :=
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (flipTwoThree.nfAll ((D.fm u).lam 0)
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colValOfTiedS_of_rest
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D →
      ∀ u : D.what₂.Word, ∃ B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u, ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  column_value_of_tie_local_bases fun D F h3 u => by
    obtain ⟨B, co, h1, h2, h3', h4⟩ := h D F h3 u
    exact ⟨B, classes_level_zero_nonempty F u, latT_of_sym F u, co, h1, h2, h3', h4⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_self_of_on {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (b : Module.Basis (Fin S.rank) E S.V) (hb : ∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) (y : S.V) :
    S.hT y y = ∑ a, star (b.repr y a) * b.repr y a := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb,
    smul_eq_mul, starRingEnd_apply]
  simp [mul_ite, Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem posFrame_of_std (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : PosFrame D := by
  obtain ⟨b, hb, -⟩ := h
  intro σ
  refine ⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩
  · haveI := b.invertibleToMatrix (D.sp.X 0).frame
    have hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det) :=
      (Matrix.isUnit_det_of_invertible _).map σ
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  · intro y
    have hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ
        fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i) := by
      intro i
      rw [← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]
      rfl
    simp only [hrepr]
    rw [hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem colBase_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho :=
  ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho

theorem colValOfTiedS_of_rest'
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → Formalism.MainNotions.flipTwoThree.adm3 D → ∀ u : D.what₂.Word,
      ∃ rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL), ∀ B : ColBase D u, B.rho = rho → ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  refine colValOfTiedS_of_rest fun D F ha u => ?_
  obtain ⟨rho, hr⟩ := h D F ha u
  obtain ⟨B, hB⟩ := colBase_of_sym F u rho
  exact ⟨B, hr B hB⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section
noncomputable section

open NumberField Matrix IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

abbrev Pol0 (D : D7) : Type := MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL

def rd (F : Pol0 D) (z : (D.mem u).C.Y 0) : ℂ :=
  fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL F) (T.val0.eY z)

theorem rd_add (F F' : Pol0 D) (z : (D.mem u).C.Y 0) : rd T (F + F') z = rd T F z + rd T F' z := by
  simp only [rd, map_add, Pi.add_apply]

theorem map_smul_LL (a : D.what₂.LL) (F : Pol0 D) :
    MvPolynomial.map D.what₂.embLL (a • F) = D.what₂.embLL a • MvPolynomial.map D.what₂.embLL F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem rd_smul (a : D.what₂.LL) (F : Pol0 D) (z : (D.mem u).C.Y 0) : rd T (a • F) z = D.what₂.embLL a * rd T F z := by
  simp only [rd, map_smul_LL, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]

theorem rd_unique {F F' : Pol0 D} (h : ∀ z, rd T F z = rd T F' z) : F = F' := by
  apply MvPolynomial.map_injective _ D.what₂.embLL.injective
  apply Formalism.L2.Col.fnOf_injective _ _ 1 (fun _ => by simp) (Formalism.MainNotions.Ext.Lw.frOne _)
  funext y
  have := h (T.val0.eY.symm y)
  simpa [rd] using this

theorem exists_pol (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ∃ F ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0), ∀ z, (D.fm u).emb 0 x c z = rd T F z := by
  obtain ⟨-, h⟩ := (T.val0.rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  obtain ⟨P, hP, hz⟩ := h c
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG D.what₂.embLL _ hP
  exact ⟨F, hF, hz⟩

def pol (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : Pol0 D := (exists_pol T x c).choose

theorem pol_mem (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    pol T x c ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0) := (exists_pol T x c).choose_spec.1

theorem pol_spec (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) (z : (D.mem u).C.Y 0) :
    (D.fm u).emb 0 x c z = rd T (pol T x c) z := (exists_pol T x c).choose_spec.2 z

def co0 : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → Pol0 D) where
  toFun x c := pol T x c
  map_add' x y := funext fun c => rd_unique T fun z => by
    rw [Pi.add_apply, rd_add, ← pol_spec, ← pol_spec, ← pol_spec, map_add]
    rfl
  map_smul' a x := funext fun c => rd_unique T fun z => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [rd_smul, ← pol_spec, ← pol_spec, LinearMap.map_smulₛₗ]
    rfl

theorem coefficient_map_apply (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : co0 T x c = pol T x c := rfl

theorem coefficient_map_injective : Function.Injective (co0 T) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply (D.fm u).emb_inj 0
  rw [map_zero]
  funext c z
  rw [pol_spec, ← coefficient_map_apply, hx]
  simp [rd]

theorem coefficient_map_mem_span (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    co0 T x c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0) := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq]
  exact pol_mem T x c

theorem coefficient_map_surjective (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (F : (D.mem u).C.cls 0 → Pol0 D)
    (hF : ∀ c, F c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) : ∃ x, co0 T x = F := by
  have hF' : ∀ c, F c ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0) := fun c => by
    have := hF c
    rwa [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq] at this
  have hs : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))),
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        T.cls0.lev.U.map (MulAut.conj (T.cls0.y c).1).toMonoidHom → γ = 1 := by
    intro c γ hγ
    obtain ⟨s, hs⟩ := (T.cls0.stabI_range c γ).2 hγ
    have := hst c
    rw [← hs, Subsingleton.elim s 1, map_one]
  have hFi : (fun c z => rd T (F c) z) ∈ (D.fm u).Fi 0 := by
    rw [T.val0.Fi, Formalism.MainNotions.Ext.Lw.fiC_eq_pi _ _ _ _ T.cls0.y_bij hs, Submodule.mem_pi]
    intro c _
    rw [Formalism.MainNotions.Ext.Lw.valC_eq]
    refine ⟨MvPolynomial.map D.what₂.embLL (F c), ?_, ?_⟩
    · rw [lamT_zero u, ← Formalism.MainNotions.Ext.Lw.cspan_eq]
      exact Formalism.L2.Col.map_mem_CSpan D.what₂.embLL _ _ (hF' c)
    · funext y
      simp [rd]
  obtain ⟨x, hx⟩ := (T.val0.rat (fun c z => rd T (F c) z)).2
    ⟨hFi, fun c => ⟨_, Formalism.L2.Col.map_mem_RatSpanG D.what₂.embLL _ (hF' c), fun z => rfl⟩⟩
  refine ⟨x, funext fun c => rd_unique T fun z => ?_⟩
  rw [coefficient_map_apply, ← pol_spec, hx]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end
