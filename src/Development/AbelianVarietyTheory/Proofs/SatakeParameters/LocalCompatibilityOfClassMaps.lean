import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIsoStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselWittDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQp

section
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys ValuativeRel Filter Topology

namespace GlobalTheory.TameRead

theorem toZMod_surj (g : ℕ) [Fact g.Prime] : Function.Surjective (PadicInt.toZMod (p := g)) := by
  intro a
  refine ⟨(a.val : ℤ_[g]), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem units_toZMod_surj (g : ℕ) [Fact g.Prime] :
    Function.Surjective (Units.map (PadicInt.toZMod (p := g)).toMonoidHom) := by
  have : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (toZMod_surj g)
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ (toZMod_surj g) this

theorem val_sub_one_lt (g : ℕ) [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (u : ℤ_[g])
    (hu : PadicInt.toZMod u = 1) : valuation F (e (u : ℚ_[g]) - 1) < 1 := by
  have hm : u - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  have hn : ‖u - 1‖ < 1 := PadicInt.mem_nonunits.1 hm
  have hn' : ‖((u : ℚ_[g]) - 1)‖ < 1 := by
    have : ((u - 1 : ℤ_[g]) : ℚ_[g]) = (u : ℚ_[g]) - 1 := by push_cast; rfl
    rw [← this]; exact hn
  have ht : Tendsto (fun n : ℕ => ((u : ℚ_[g]) - 1) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn'
  have ht' : Tendsto (fun n : ℕ => (e ((u : ℚ_[g]) - 1)) ^ n) atTop (𝓝 0) := by
    have := (he.tendsto 0).comp ht
    simpa [Function.comp_def, map_pow] using this
  have h1 : e ((u : ℚ_[g]) - 1) = e (u : ℚ_[g]) - 1 := by rw [map_sub, map_one]
  rw [← h1]
  exact (GlobalTheory.FlatFBCompare.val_lt_one_iff _).2 ht'

theorem exists_tamePart : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ →
    ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  intro g _ F _ _ _ _ e he ξ hξ
  let μ : ℤ_[g]ˣ →* ℂˣ := (ξ.comp (Units.map e.toMonoidHom)).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom)
  have hker : (Units.map (PadicInt.toZMod (p := g)).toMonoidHom).ker ≤ μ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hu' : PadicInt.toZMod (u : ℤ_[g]) = 1 := by
      have := congrArg (fun x : (ZMod g)ˣ => (x : ZMod g)) hu
      simpa using this
    apply hξ
    have := val_sub_one_lt g e he (u : ℤ_[g]) hu'
    simpa [μ] using this
  refine ⟨(Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfSurjective (units_toZMod_surj g) ⟨μ, hker⟩, ?_⟩
  intro u
  exact ((Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfRightInverse_comp_apply _
    (Function.rightInverse_surjInv (units_toZMod_surj g)) ⟨μ, hker⟩ u).symm

end GlobalTheory.TameRead
end

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ → ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  atlas_forward_decl GlobalTheory.TameRead.exists_tamePart
end

section
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
end

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  atlas_forward_decl GlobalTheory.SerSys.irrSm_pullback
end

section
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.ParRead

open ValuativeRel Matrix

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem lt_one_mem_nhds : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
  (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, by simp⟩

theorem val_lt_one {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (e z) ^ n) Filter.atTop (nhds 0) := by
    have := (he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)
    rw [map_zero] at this
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨n, hn⟩ := (h1.eventually lt_one_mem_nhds).exists
  rw [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem val_lt_one_of_red {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℤ_[g]}
    (hz : PadicInt.toZMod z = 0) : valuation F (e z) < 1 := by
  have : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
  exact val_lt_one he this

theorem val_le_one {e : ℚ_[g] ≃+* F} (he : Continuous e) (z : ℤ_[g]) : valuation F (e z) ≤ 1 := by
  set m : ℕ := (PadicInt.toZMod z).val
  have hm : PadicInt.toZMod (z - (m : ℤ_[g])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have e1 : e (z : ℚ_[g]) = (m : F) + e ((z - (m : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; ring
  rw [e1]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (val_lt_one_of_red he hm).le)
  clear e1 hm
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

def intHom {e : ℚ_[g] ≃+* F} (he : Continuous e) : ℤ_[g] →+* 𝒪[F] :=
  (e.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).codRestrict 𝒪[F] fun z => by
    rw [Valuation.mem_integer_iff]; exact val_le_one he z

theorem map_inc_mem_KO {e : ℚ_[g] ≃+* F} (he : Continuous e) {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map e.toRingHom (inc g n k) ∈ GlobalTheory.SplitWeil.KO F (Fin n) := by
  refine ⟨Matrix.GeneralLinearGroup.map (intHom he) k, ?_⟩
  ext i j
  simp [inc, intHom]
  rfl

theorem act_inc {e : ℚ_[g] ≃+* F} (he : Continuous e) {ξ : Fˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ}
    (hT : TamePart (ξ.comp (Units.map e.toMonoidHom)) χ) {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin (r + t)) F) V} {u : V} (hu : GlobalTheory.SplitRead.IsBlockVec ξ ρ u)
    (k : GL (Fin (r + t)) ℤ_[g]) (h0 : InPar r (red g (r + t) k : Mt g (r + t)))
    (h1 : tl r (red g (r + t) k : Mt g (r + t)) = 1) (c : (ZMod g)ˣ)
    (hc : (c : ZMod g) = (br r t (red g (r + t) k : Mt g (r + t))).det) :
    ρ (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)) u = ((χ c : ℂˣ) : ℂ) • u := by
  have hred : ∀ i j, (red g (r + t) k : Mt g (r + t)) i j = PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j) :=
    fun i j => by simp [red]
  have hent : ∀ i j, (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)).val i j =
      e ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j : ℚ_[g]) := fun i j => by simp [inc]
  set d : ℤ_[g] := ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)).det with hd
  have hbr : br r t (red g (r + t) k : Mt g (r + t)) =
      (PadicInt.toZMod (p := g)).mapMatrix ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    ext i j
    have hi : r + (i : ℕ) < r + t := by omega
    have hj : r + (j : ℕ) < r + t := by omega
    simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), hred]
    rfl
  have hdc : PadicInt.toZMod d = c := by rw [hc, hbr, hd, RingHom.map_det]
  have hdu : IsUnit d := by
    by_contra h
    have : d ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, hdc] at this
    exact c.ne_zero this
  refine (hu _ (map_inc_mem_KO he k) ?_ ?_
    (Units.map e.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hdu.unit)) ?_).trans ?_
  · intro i j
    rw [hent]
    apply val_lt_one_of_red he
    rw [← hred]
    exact h0 _ _ (by simp) (by simp)
  · intro i j
    rw [hent]
    have hij : (red g (r + t) k : Mt g (r + t)) (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Mt g r) i j := by
      rw [← h1]
      have hi : (i : ℕ) < r + t := by omega
      have hj : (j : ℕ) < r + t := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj)]
      rfl
    have h2 : PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) (Fin.castAdd t i) (Fin.castAdd t j) -
        if i = j then 1 else 0) = 0 := by
      rw [map_sub, ← hred, hij, Matrix.one_apply]
      split_ifs <;> simp
    have := val_lt_one_of_red he h2
    convert this using 2
    split_ifs <;> simp
  · simp [hd, RingHom.map_det]
    congr 1
  · have h2 := hT hdu.unit
    have h3 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom hdu.unit = c := Units.ext (by simpa using hdc)
    rw [h3, MonoidHom.comp_apply] at h2
    rw [h2]

theorem inPar_one {r n : ℕ} : InPar r (1 : Mt g n) := fun i j hj hi => by
  rw [Matrix.one_apply_ne]
  intro h; rw [h] at hi; omega

theorem tl_one {r t : ℕ} : tl r (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : (i : ℕ) < r + t := by omega
  have hj : (j : ℕ) < r + t := by omega
  simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]

theorem br_one {r t : ℕ} : br r t (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : r + (i : ℕ) < r + t := by omega
  have hj : r + (j : ℕ) < r + t := by omega
  simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

theorem blk_parts {r t : ℕ} (y : Gn g t) :
    InPar r (blk r t (r + t) 1 y : Mt g (r + t)) ∧ tl r (blk r t (r + t) 1 y : Mt g (r + t)) = 1 ∧
      br r t (blk r t (r + t) 1 y : Mt g (r + t)) = (y : Mt g t) := by
  set M : Mt g (r + t) := fun i j : Fin (r + t) =>
    if (i : ℕ) < r ∧ (j : ℕ) < r then Formalism.MainNotions.ArithmeticCylinders.entN ((1 : Gn g r) : Mt g r) i j
    else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g t) (i - r) (j - r) else 0 with hM
  have h0 : InPar r M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = 1 := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hM, hi, hj]
  have h2 : br r t M = y := by
    ext i j
    simp [br, Formalism.MainNotions.ArithmeticCylinders.entN, hM]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, LabelDet.det_inPar r t M h0, h1, h2, Matrix.det_one, one_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have hb : (blk r t (r + t) 1 y : Mt g (r + t)) = M := by
    show ((toG M : Gn g (r + t)) : Mt g (r + t)) = M
    rw [toG, dif_pos hu]; rfl
  rw [hb]; exact ⟨h0, h1, h2⟩

theorem isParVec_of_isBlockVec : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ),
    TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u →
    IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  intro g _ F _ _ _ _ e he ξ χ hT r t V _ _ ρ u hu
  have hsurj : ∀ x : Gn g (r + t), red g (r + t) (Function.invFun (red g (r + t)) x) = x :=
    fun x => Function.invFun_eq (Model.red_surjective _ x)
  refine ⟨?_, ?_, ?_⟩
  · rw [Model.mem_principalCongruenceFixedVectors_iff]
    intro k hk
    have := act_inc he hT hu k (by rw [hk, Units.val_one]; exact inPar_one) (by rw [hk, Units.val_one]; exact tl_one) 1
      (by rw [hk, Units.val_one, Units.val_one, br_one, Matrix.det_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro x h0 h1 h2
    have := act_inc he hT hu (Function.invFun (red g (r + t)) x) (by rw [hsurj]; exact h0) (by rw [hsurj]; exact h1) 1
      (by rw [hsurj, h2, Matrix.det_one, Units.val_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro y
    obtain ⟨h0, h1, h2⟩ := blk_parts (r := r) y
    have := act_inc he hT hu (Function.invFun (red g (r + t)) (blk r t (r + t) 1 y)) (by rw [hsurj]; exact h0)
      (by rw [hsurj]; exact h1) (Matrix.GeneralLinearGroup.det y)
      (by rw [hsurj, h2, Matrix.GeneralLinearGroup.val_det_apply])
    exact this

end GlobalTheory.ParRead
end
end

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ), TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u → IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  atlas_forward_decl GlobalTheory.ParRead.isParVec_of_isBlockVec
end

section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) → ∀ (h : GL (Fin r) (ZMod g)) (h' : GL (Fin (r + t)) F), GlobalTheory.PendOf.IsLiftN h h' → ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  first | exact @GlobalTheory.SerSys.BlockLift.blockLift_act | exact GlobalTheory.SerSys.BlockLift.blockLift_act | (intros; apply GlobalTheory.SerSys.BlockLift.blockLift_act <;> assumption)
end

section
universe u_1 u_2 u_3

namespace GlobalTheory.IntertwiningFunctional

private theorem freeAlgebra_lift_intertwine {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V) (T : V →ₗ[ℂ] F)
    (hT : ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) (a : FreeAlgebra ℂ K) :
    ∀ v : V, T (FreeAlgebra.lift ℂ ρ a v) = FreeAlgebra.lift ℂ r a (T v) := by
  induction a using FreeAlgebra.induction with
  | grade0 c => intro v; simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | grade1 k => intro v; simp [FreeAlgebra.lift_ι_apply, hT]
  | mul a b ha hb => intro v; simp only [map_mul, Module.End.mul_apply]; rw [ha, hb]
  | add a b ha hb => intro v; simp only [map_add, LinearMap.add_apply]; rw [ha, hb]

theorem exists_intertwining_functional {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ (W : Submodule ℂ V), (∀ (k : K), ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop)
    (hP : ∀ (T : V →ₗ[ℂ] F), P T → ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) :
    ∀ f ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T, f ≠ (0 : F) →
      ∃ (φ : F →ₗ[ℂ] V), φ f ≠ (0 : V) ∧ ∀ (k : K),
        ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T,
          φ (r k f') = ρ k (φ f') := by
  classical
  intro f hf hf0
  set S := ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T with hSdef

  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply hf0
    have hS : S = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun T _ => ?_)
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
      exact Submodule.zero_mem _
    rw [hS, Submodule.mem_bot] at hf
    exact hf

  let A := FreeAlgebra ℂ K
  let rA : A →ₐ[ℂ] Module.End ℂ F := FreeAlgebra.lift ℂ r
  let ρA : A →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ ρ
  let : Module A F := Module.compHom F rA.toRingHom
  let : Module A V := Module.compHom V ρA.toRingHom
  have smulF : ∀ (a : A) (x : F), a • x = rA a x := fun _ _ => rfl
  have smulV : ∀ (a : A) (x : V), a • x = ρA a x := fun _ _ => rfl
  have : IsScalarTower ℂ A F := ⟨fun c a x => by
    rw [smulF, smulF, map_smul, LinearMap.smul_apply]⟩
  have : IsScalarTower ℂ A V := ⟨fun c a x => by
    rw [smulV, smulV, map_smul, LinearMap.smul_apply]⟩
  have hιF : ∀ (k : K) (x : F), (FreeAlgebra.ι ℂ k : A) • x = r k x := fun k x => by
    show FreeAlgebra.lift ℂ r (FreeAlgebra.ι ℂ k) x = r k x
    rw [FreeAlgebra.lift_ι_apply]
  have hιV : ∀ (k : K) (v : V), (FreeAlgebra.ι ℂ k : A) • v = ρ k v := fun k v => by
    show FreeAlgebra.lift ℂ ρ (FreeAlgebra.ι ℂ k) v = ρ k v
    rw [FreeAlgebra.lift_ι_apply]

  have hVs : IsSimpleModule A V := by
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => ?_ }
    have hWinv : ∀ (k : K), ∀ v ∈ W.restrictScalars ℂ, ρ k v ∈ W.restrictScalars ℂ := by
      intro k v hv
      rw [← hιV]
      exact W.smul_mem _ hv
    rcases hirr (W.restrictScalars ℂ) hWinv with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

  let mkA : ∀ T : V →ₗ[ℂ] F, (∀ (k : K) (v : V), T (ρ k v) = r k (T v)) → V →ₗ[A] F :=
    fun T hT =>
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun a v => freeAlgebra_lift_intertwine r ρ T hT a v }
  let p : (V →ₗ[ℂ] F) → Submodule A F := fun T =>
    if h : ∀ (k : K) (v : V), T (ρ k v) = r k (T v) then LinearMap.range (mkA T h) else ⊥
  let s : Set (V →ₗ[ℂ] F) := {T | P T}
  let SA : Submodule A F := ⨆ T ∈ s, p T
  have hpT : ∀ T (hT : T ∈ s), p T = LinearMap.range (mkA T (hP T hT)) :=
    fun T hT => dif_pos (hP T hT)
  have hpSA : ∀ T (hT : T ∈ s), p T ≤ SA := fun T hT =>
    le_iSup₂ (f := fun T (_ : T ∈ s) => p T) T hT
  have memSA : ∀ x : F, x ∈ S ↔ x ∈ SA := by
    intro x
    constructor
    · intro hx
      have hle : S ≤ SA.restrictScalars ℂ := by
        refine iSup₂_le fun T hT => ?_
        rintro _ ⟨v, rfl⟩
        have h1 : T v ∈ p T := by
          rw [hpT T hT]
          exact ⟨v, rfl⟩
        exact hpSA T hT h1
      exact hle hx
    · intro hx
      refine Submodule.iSup_induction (fun T => ⨆ (_ : T ∈ s), p T) (motive := fun y => y ∈ S)
        hx ?_ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
      intro T y hy
      by_cases hT : T ∈ s
      · have hy' : y ∈ p T := (iSup_le fun _ => le_rfl : (⨆ (_ : T ∈ s), p T) ≤ p T) hy
        rw [hpT T hT] at hy'
        obtain ⟨v, rfl⟩ := hy'
        exact (le_iSup₂ (f := fun T (_ : P T) => LinearMap.range T) T hT : _ ≤ S) ⟨v, rfl⟩
      · rw [iSup_neg hT, Submodule.mem_bot] at hy
        rw [hy]
        exact Submodule.zero_mem _

  have : IsSemisimpleModule A SA :=
    isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun T hT => by
      rw [hpT T hT]
      exact IsSemisimpleModule.range _)
  let f₀ : SA := ⟨f, (memSA f).mp hf⟩
  have hf₀ : f₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)

  obtain ⟨m, hmN, hm⟩ : ∃ m ≤ Submodule.span A {f₀}, IsSimpleModule A m := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span A {f₀}) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hf₀
    · exact h
  have := hm
  have : Nontrivial m := IsSimpleModule.nontrivial A m
  obtain ⟨q, hq⟩ := exists_isCompl m
  let π : SA →ₗ[A] m := Submodule.projectionOnto m q hq
  have hπleft : ∀ y : m, π y = y := fun y => Submodule.projectionOnto_apply_left hq y
  have hπf : π f₀ ≠ 0 := by
    intro h0
    have hNk : Submodule.span A {f₀} ≤ LinearMap.ker π := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h0
    obtain ⟨y, hy0⟩ := exists_ne (0 : m)
    apply hy0
    have hyk : (y : SA) ∈ LinearMap.ker π := hNk (hmN y.2)
    rw [LinearMap.mem_ker, hπleft] at hyk
    exact hyk

  have hmemT : ∀ T (hT : T ∈ s) (v : V), mkA T (hP T hT) v ∈ SA := fun T hT v =>
    hpSA T hT (by rw [hpT T hT]; exact ⟨v, rfl⟩)
  obtain ⟨T, hT, hg⟩ : ∃ T, ∃ hT : T ∈ s,
      π ∘ₗ LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hπf
    have hle : SA ≤ (LinearMap.ker π).map SA.subtype := by
      refine iSup₂_le fun T hT => ?_
      rw [hpT T hT]
      rintro _ ⟨v, rfl⟩
      refine ⟨LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) v, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, hne T hT, LinearMap.zero_apply]
    obtain ⟨y, hy, hyf⟩ := hle f₀.2
    have hyeq : y = f₀ := Subtype.ext hyf
    rw [← hyeq]
    exact hy
  let e : V ≃ₗ[A] m := LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hg)
  let φ₀ : SA →ₗ[A] V := e.symm.toLinearMap ∘ₗ π
  have hφ₀f : φ₀ f₀ ≠ 0 := by
    intro h
    apply hπf
    have h1 : e (φ₀ f₀) = π f₀ := e.apply_symm_apply (π f₀)
    rw [← h1, h, map_zero]

  let ψ : S →ₗ[ℂ] V :=
    { toFun := fun x => φ₀ ⟨x.1, (memSA x.1).mp x.2⟩
      map_add' := fun x y => by
        rw [← map_add]
        rfl
      map_smul' := fun c x => by
        have h1 : (⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ : SA) =
            algebraMap ℂ A c • (⟨x.1, (memSA _).mp x.2⟩ : SA) :=
          Subtype.ext (algebraMap_smul (A := A) c x.1).symm
        show φ₀ ⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ = c • φ₀ ⟨x.1, (memSA _).mp x.2⟩
        rw [h1, map_smul, algebraMap_smul] }
  obtain ⟨φ, hφext⟩ := LinearMap.exists_extend ψ
  have hφ : ∀ (x : F) (hx : x ∈ S), φ x = φ₀ ⟨x, (memSA x).mp hx⟩ := fun x hx =>
    LinearMap.congr_fun hφext ⟨x, hx⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ f hf]
    exact hφ₀f
  · intro k x hx
    have hrk : r k x = (FreeAlgebra.ι ℂ k : A) • x := (hιF k x).symm
    have hmem : r k x ∈ S := by
      rw [memSA, hrk]
      exact SA.smul_mem _ ((memSA _).mp hx)
    rw [hφ _ hmem, hφ _ hx, ← hιV k, ← map_smul φ₀]
    congr 1
    exact Subtype.ext hrk

end GlobalTheory.IntertwiningFunctional
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepLoc

theorem exists_sep {K F V : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ W : Submodule ℂ V, (∀ k, ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop) (hP : ∀ T, P T → ∀ k v, T (ρ k v) = r k (T v))
    (f : F) (hf : f ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T) (hf0 : f ≠ 0) :
    ∃ φ : F →ₗ[ℂ] V, φ f ≠ 0 ∧ ∀ k, ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T,
      φ (r k f') = ρ k (φ f') := by
  first
  | exact @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | (apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional ..)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL f hf hf0
  have hle := GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hcL
  have hirr : ∀ W : Submodule ℂ σ.V, (∀ k : {x : GAf L n // TrivOutside {s.v} x}, ∀ v ∈ W,
      σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let R : Subrepresentation σ.ρ := ⟨W, fun g v hv => by
      obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
      have hg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = g := by
        rw [hxe]; ext i j; simp
      have := hW ⟨x, hx⟩ v hv
      rwa [hg] at this⟩
    haveI := σ.irr
    rcases eq_bot_or_eq_top R with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  obtain ⟨φ, hφf, hφ⟩ := exists_sep (K := {x : GAf L n // TrivOutside {s.v} x}) (fun k => NG.rt L n k.1)
    (fun k => σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1))) hirr
    (fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) => (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v,
      T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v))
    (fun T hT k v => hT.2 k.1 k.2 v) f (hle hf) hf0
  exact ⟨φ, hφf, fun x hx f' hf' => hφ ⟨x, hx⟩ f' (hle hf')⟩

end GlobalTheory.SepLoc
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_local_component_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  atlas_forward_decl GlobalTheory.SepLoc.main
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf

set_option maxHeartbeats 1000000 in
theorem blockEig (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (PI : D.naut.AV i)
    (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (s : SplitPlace D.host.E)
    (hsw : s.w = D.naut.plGw k v) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hcont : Continuous c) (hci : ∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (x : GAf D.host.E D.R.nV) (hx : TrivOutside {s.v} x)
    (hh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
      GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t) :
    NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w)
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ : GlobalTheory.NPin.IsComp (P.tp.tup (D.nd.mu i) j) s.w ((P.tp.tup (D.nd.mu i) j).loc s.w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci ((P.tp.tup (D.nd.mu i) j).loc s.w) ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h =
      ((((P.tp.tup (D.nd.mu i) j).loc s.w) (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]

set_option maxHeartbeats 2000000 in
theorem compAt (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
    ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ), TamePart μ χ ∧
      D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 μ)) ∧
      ∀ Q : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧ D.naut.locV i Q w = rcw D.R.nV π ∧
        ActsThrough π D.R.r D.R.t χ (D.naut.typeV i Q)
          fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) := by
  classical
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hsp : IsSplitPl D.host w := hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hsp
  subst hs
  have htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w) :=
    GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame
  refine ⟨_, χ, hχ, GlobalTheory.T.local_langlands_split_qp hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
  have hσ' : IsLocS (n := D.R.nV) (P.H.av.S i Q) s σ := hσ
  refine ⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩
  · apply (P.T.e s.w).injective
    rw [hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ hσ'
  obtain ⟨c, T, hc, hci, -, -, -⟩ := hσ
  set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ
  have hT : ∀ F, F ∈ D.naut.typeV i Q ↔
      (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun F => by
    rw [P.H.av.typeV]; exact Submodule.mem_comap
  let J := {φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x →
    ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q),
      φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}
  let ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V) :=
    LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)
  have hpar : ∀ (φ : J) (F : D.naut.typeV i Q),
      IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F)) := by
    intro φ F
    refine GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_
    refine GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_
    obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h := by
      rw [hxe]; exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
    have hF := (hT F).1 F.2
    have hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
        GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := by rw [hmap]; exact hh
    have h3 := φ.2 x hx _ hF
    rw [blockEig hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
    rw [← hmap]; exact h3.symm
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    by_contra hne
    have h1 : (P.M.loc i).real F ≠ 0 := fun h0 =>
      hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))
    obtain ⟨φ, hφ, hφe⟩ := GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _
      ((hT F).1 F.2) h1
    exact hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)
  refine ⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩
  have hzc : ∀ b, a * b = b * a := fun b => (Subalgebra.mem_center_iff.1 ha b).symm
  have hcz := GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc
  obtain ⟨L, hLift, hCL⟩ := hCen i
  have e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dif_pos hcz]; exact hCL ⟨_, hcz⟩ F
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧
      IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧
      NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    GlobalTheory.T.lift_through_completion_iso hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
      (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hF := (hT F).1 F.2
  have e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) := by
    rw [e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]
  have hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q := by
    rw [hT, e1]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)
  refine ⟨hmem, fun φ => ?_⟩
  have hu := (hpar φ F).1
  change φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) =
    actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))
  rw [e1, map_sum, actTop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]
  congr 1
  exact GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL P.T I rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → LocComp D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => compAt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩

end GlobalTheory.LocCompTy
end
