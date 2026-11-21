import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmpW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : AddSubgroup (Mx F E d.m d.n) where
  carrier := {X | d.cw w X = 0}
  zero_mem' := by
    show d.cw w 0 = 0
    exact Matrix.map_zero _ (map_zero _)
  add_mem' := by
    intro X Z hX hZ
    show d.cw w (X + Z) = 0
    have e : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
    rw [e, show d.cw w X = 0 from hX, show d.cw w Z = 0 from hZ, add_zero]
  neg_mem' := by
    intro X hX
    show d.cw w (-X) = 0
    have e : d.cw w (-X) = -d.cw w X := Matrix.map_neg _ (map_neg _) X
    rw [e, show d.cw w X = 0 from hX, neg_zero]
def IntFact_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ν : Measure (Mx F E d.m d.n)), d.IsCov ν →
  ∃ (C : ℝ) (μ' : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)), 0 < C ∧ μ'.IsAddHaarMeasure ∧
    ∀ (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ),
      (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
      ∫ X, R.tens w f Ψ X ∂ν = C * (∫ u, f u) * ∫ Z, Ψ Z.1 ∂μ'
section Split
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_add'_k (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z := Matrix.map_add _ (map_add _) X Z
theorem cw_sub'_k (X Z : Mx F E d.m d.n) : d.cw w (X - Z) = d.cw w X - d.cw w Z := Matrix.map_sub _ (map_sub _) X Z
theorem loc_add'_k (X Z : Mx F E d.m d.n) : R.loc w (X + Z) = R.loc w X + R.loc w Z := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add'_k, Matrix.mul_add]
  exact Matrix.map_add _ (fun a b => star_add a b) _ _
theorem loc_of_mem_k {b : Mx F E d.m d.n} (hb : b ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) : R.loc w b = 0 := by
  have h : d.cw w b = 0 := hb
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [h, Matrix.mul_zero]
  exact Matrix.map_zero _ (star_zero _)
theorem continuous_loc_k : Continuous (R.loc w) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  exact (continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w)).matrix_map continuous_star
end Split
theorem intFact_k : _root_.PositivityTheory.SiegelWeilFormula.KFock.IntFact_k := by
  intro F E _ _ _ _ _ σ d R w ν hν
  haveI := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (_root_.PositivityTheory.SiegelWeilFormula.Place.continuous_cw_k d w) continuous_const
  haveI : LocallyCompactSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w) := Subtype.borelSpace ((_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr
  let U : (Fin d.m → Fin d.n → ℂ) → Matrix (Fin d.m) (Fin d.n) ℂ := fun u => fr * Matrix.of fun b j => star (u b j)
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then U u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = U u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = U u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have inv_fr : ((R.fr w)⁻¹).1 * fr = 1 := Units.inv_mul (R.fr w)
  have fr_inv : fr * ((R.fr w)⁻¹).1 = 1 := Units.mul_inv (R.fr w)
  have loc_sW : ∀ u, R.loc w (sW u) = u := fun u => by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
    rw [cw_sW, ← Matrix.mul_assoc, inv_fr, Matrix.one_mul]
    ext a j
    simp
  have U_loc : ∀ X, U (R.loc w X) = d.cw w X := fun X => by
    simp only [U, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
    have : (Matrix.of fun b j => star ((((R.fr w)⁻¹).1 * d.cw w X).map star b j)) = ((R.fr w)⁻¹).1 * d.cw w X := by
      ext b j; simp
    rw [this, ← Matrix.mul_assoc, fr_inv, Matrix.one_mul]
  have U_add : ∀ u v, U (u + v) = U u + U v := fun u v => by
    simp only [U]
    rw [← Matrix.mul_add]
    congr 1
    ext b j
    simp [star_add]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then U u i j else 0) + (if w' = w then U v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h, U_add]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hU : Continuous U := by
    simp only [U]
    exact continuous_const.matrix_mul (continuous_pi fun b => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp (continuous_apply b)))
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hU)
    · exact continuous_const
  have mem : ∀ X, X - sW (R.loc w X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w := fun X => by
    show d.cw w (X - sW (R.loc w X)) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_sub'_k, cw_sW, U_loc, sub_self]
  let Φ : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (R.loc w X, ⟨X - sW (R.loc w X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have e1 : R.loc w (sW u + b) = u := by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero]
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (R.loc w (sW u + b)) = b
        rw [e1, add_sub_cancel_left]
      right_inv := fun X => by
        show sW (R.loc w X) + (X - sW (R.loc w X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w).prodMk
        ((continuous_id.sub (hsW.comp (_root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_loc_k d R w))).subtype_mk _) }
  obtain ⟨C, hC, hg⟩ := integral_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)) Φ
  refine ⟨C, Measure.addHaar, hC, inferInstance, fun f Ψ hΨ => ?_⟩
  rw [hg]
  have e : ∀ p : (Fin d.m → Fin d.n → ℂ) × _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w, R.tens w f Ψ (Φ p) = f p.1 * Ψ p.2.1 := fun p => by
    obtain ⟨u, b, hb⟩ := p
    show f (R.loc w (sW u + b)) * Ψ (sW u + b) = f u * Ψ b
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k, loc_sW, _root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w hb, add_zero, add_comm, hΨ b (sW u) (cw_sW' u) (fin_sW u)]
  simp_rw [e]
  have hp := integral_prod_mul (μ := (volume : Measure (Fin d.m → Fin d.n → ℂ))) (ν := (Measure.addHaar : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w)))
    f (fun Z : _root_.PositivityTheory.SiegelWeilFormula.KFock.cmpW_k d w => Ψ Z.1)
  rw [hp, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def insW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F)
theorem insW_self_k (z : ℂ) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_same]
theorem insW_ne_k {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_of_ne hw]
theorem insW_fin_k (z : ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.2.1]
theorem insW_add_k (z z' : ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w (z + z') = _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z + _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, Pi.single_add, h.2.2.2.1]
end
def insL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w)
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def Supp_k (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0
theorem cw_insL_k (v : Fin d.m → Fin d.n → ℂ) : d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_self_k]
theorem insL_supp_k (v : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_ne_k d w hw', Matrix.zero_apply]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_fin_k, Matrix.zero_apply]
theorem insL_add_k (v v' : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (v + v') = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_add_k]
theorem insL_zero_k : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = 0 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k R w 0 0
  rw [add_zero] at h
  calc _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by abel
    _ = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by rw [← h]
    _ = 0 := sub_self _
theorem insL_loc_k {Z : Mx F E d.m d.n} (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w Z
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w' Z
      rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).1 w' hw, hZ.1 w' hw]
  · rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).2, hZ.2]
theorem rest_inv_k (X Z : Mx F E d.m d.n) (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) :
    (X + Z) - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w (X + Z)) = X - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w X) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k d R w X Z, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_loc_k R w hZ]
  abel
end
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem psi_add_right_k (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add, mul_add, AddChar.map_add_eq_mul]
theorem psi_add_left_k (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add, mul_add, AddChar.map_add_eq_mul]
theorem cw_gram_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]
theorem gram_supp_cmp_k (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  · unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp
theorem psi_zero_gram_k (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
end
theorem zeta_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_loc_k (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
theorem frJ_k : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]
end
theorem psi_at_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]
theorem kernel_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) = 0 := by
    intro w' hw
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u) = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) = (finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).2]
    simp
  have e1 : d.cw w (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_at_w_k d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KW
end
end
end
