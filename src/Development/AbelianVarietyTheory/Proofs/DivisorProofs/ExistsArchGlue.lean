import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

section
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwSplitLine

theorem iwasawa_line_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  obtain ⟨P, P', hne, hP, hP'⟩ := hv
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (v := v) hne (IsDedekindDomain.HeightOneSpectrum.ext hP) (IsDedekindDomain.HeightOneSpectrum.ext hP')
  obtain ⟨k, i, qq, hn, hsum⟩ := GlobalTheory.IwSplitFrame.exists_compl x y (cT (σ : E →+* E) y * J) (cT (σ : E →+* E) x * J)
    hyx hyy hxx hxy
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ
    (e := x) (e' := y) (i := i) (p := cT (σ : E →+* E) y * J) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum hxy
  have hQ : ∀ z : GLoc σ J v, (B⁻¹ * splitHom σ J τ z * B).1.BlockTriangular lv →
      z ∈ GlobalTheory.IwSplitFrame.keepGrp (σ := σ) (J := J) (v := v) (x.map (inclR (F := F) (Fv F v))) :=
    fun z hz => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB z hz
      exact GlobalTheory.IwSplitFrame.keeps_of_split h τ z hyx hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular h hJ τ L hL _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  exact ⟨q, k', hk, rfl, β, hβ⟩

end GlobalTheory.IwSplitLine
end
end

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_lattice_local_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  atlas_forward_decl GlobalTheory.IwSplitLine.iwasawa_line_split
end

section
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

open IsDedekindDomain

namespace GlobalTheory.InertIwasawaUnram

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ hσ hU n J hJ x y hx hy L hL v hv hSD g
  haveI := hL
  obtain ⟨c, hc⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hσ inferInstance
  have hram : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.ramificationIdx (𝓞 F) = 1 := fun P => by
    haveI := P.isPrime
    haveI : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := inferInstance
    exact Ideal.ramificationIdx_eq_one _ _
  have hUn : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := fun P _ => hram P
  have hIU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := fun P _ => hram P
  obtain ⟨w, hw⟩ := ((GlobalTheory.LFun.exists_isInertChart σ hσ v).1 hIU).resolve_left hv
  obtain ⟨q, k, hk, hg, β, hβ⟩ := GlobalTheory.InertIwasawaLoc.exists_loc hσ hc hJ hw hUn hSD
    (e := x) (p := cT (σ : E →+* E) y * J) (by rw [Matrix.mul_assoc] at hy ⊢; exact hy) hx g
  exact ⟨q, k, hk, hg, β, hβ⟩

end GlobalTheory.InertIwasawaUnram
end

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_lattice_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  atlas_forward_decl GlobalTheory.InertIwasawaUnram.main
end

section
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwArchLine

theorem form_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m k l : Type} [Fintype m] (M : Matrix m k E) (J : Matrix m m E) (N : Matrix m l E) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) * J.map (inclR (F := F) R) * N.map (inclR (F := F) R) =
      (cT (σ : E →+* E) M * J * N).map (inclR (F := F) R) := by
  have h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) = (cT (σ : E →+* E) M).map (inclR (F := F) R) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [h1, Matrix.map_mul, Matrix.map_mul]

theorem exists_q_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  intro F E _ _ _ _ _ σ hcm n J _ x y hx hxy a ha w g
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := ha w
  have hXiso := form_map_inclR (F := F) w.Completion σ x J x
  rw [hx, Matrix.map_zero _ (map_zero _)] at hXiso
  obtain ⟨K, hK, hK1, β, hβ⟩ := GlobalTheory.Core.Rk.IwArch.iw_iso_cols (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ)
    (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ) (fun z => (GlobalTheory.AdelicU.infEmb_sigR hcm τ z).symm)
    (bc (compInf F E w) a) ε hε _ hXiso (GlobalTheory.AdelicU.matHom w.Completion σ J g) g.2
  let kk : GArch σ J w := ⟨K, hK⟩
  have hPX := form_map_inclR (F := F) w.Completion σ y J x
  rw [hxy, Matrix.map_one _ (map_zero _) (map_one _)] at hPX
  set X := x.map (inclR (F := F) w.Completion) with hXdef
  set P := cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (y.map (inclR (F := F) w.Completion)) *
    J.map (inclR (F := F) w.Completion) with hPdef
  set Q : GL (Fin n) (w.Completion ⊗[F] E) := GlobalTheory.AdelicU.matHom w.Completion σ J g * K⁻¹ with hQ
  have hQX : Q.1 * X = X * β := hβ
  have hX' : X = (Q⁻¹).1 * X * β := by
    rw [Matrix.mul_assoc, ← hQX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hleft : (P * (Q⁻¹).1 * X) * β = 1 := by
    rw [← hPX]; conv_rhs => rw [hX']
    simp only [Matrix.mul_assoc]
  let βu : GL (Fin 1) (w.Completion ⊗[F] E) := ⟨β, P * (Q⁻¹).1 * X, mul_eq_one_comm.1 hleft, hleft⟩
  refine ⟨g * kk⁻¹, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group, βu, ?_⟩
  have : (GlobalTheory.AdelicU.matHom w.Completion σ J (g * kk⁻¹)) = Q := by
    rw [map_mul, map_inv]; rfl
  rw [this]; exact hQX

end GlobalTheory.IwArchLine
end

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_iwasawa_majorant_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  atlas_forward_decl GlobalTheory.IwArchLine.exists_q_k
end

section
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.LineGlue

theorem map_mul_eq_of_local {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (U : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin 1) R) (P : Matrix (Fin 1) (Fin n) R)
    (hPX : P * X = 1) (β : Matrix (Fin 1) (Fin 1) S) (h : U.map φ * X.map φ = X.map φ * β) :
    (U * X).map φ = (X * (P * U * X)).map φ := by
  have hβ : (P * U * X).map φ = β := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hPX,
      Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul]
  rw [Matrix.map_mul, h, ← hβ, ← Matrix.map_mul]

end GlobalTheory.LineGlue

theorem GlobalTheory.LineGlue.exists_idele_smul_of_local_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  intro F E _ _ _ _ _ σ n J x pL hpx q hInf hFin
  set U := matHom (AF F) σ J q with hU
  set X := adMat F x with hX
  set P := pL.map (inclR (F := F) (AF F)) with hP
  have hPX : P * X = 1 := by
    rw [hP, hX, adMat, ← Matrix.map_mul, hpx, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinclFin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      x.map (inclR (F := F) (Fv F v)) = X.map (compFin F E v) := by
    intro v
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compFin, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hinclInf : ∀ w : InfinitePlace F,
      x.map (inclR (F := F) w.Completion) = X.map (compInf F E w) := by
    intro w
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compInf, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hMX : U.1 * X = X * (P * U.1 * X) := by
    ext i j
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun v => ?_)
    · obtain ⟨β, hβ⟩ := hInf w
      rw [matHom_projArch, hinclInf] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compInf F E w) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
    · obtain ⟨β, hβ⟩ := hFin v
      rw [matHom_proj, hinclFin] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compFin F E v) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
  obtain ⟨c', hc'⟩ : ∃ c' : AF F ⊗[F] E, c' * (P * U.1 * X) 0 0 = 1 := by
    refine ⟨(P * (U⁻¹).1 * X) 0 0, ?_⟩
    have h1 : X = (U⁻¹).1 * X * (P * U.1 * X) := by
      rw [Matrix.mul_assoc, ← hMX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h2 : P * (U⁻¹).1 * X * (P * U.1 * X) = 1 := by
      rw [show P * (U⁻¹).1 * X * (P * U.1 * X) = P * ((U⁻¹).1 * X * (P * U.1 * X)) by
        simp only [Matrix.mul_assoc], ← h1, hPX]
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using this
  refine ⟨Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hc'), ?_⟩
  rw [hMX]
  ext i j
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]
end

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_archimedean_eigenvector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  atlas_forward_decl GlobalTheory.LineGlue.exists_idele_smul_of_local_lines
end

section
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwasawaTriv

theorem absE_eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ hσ n J L hL a x pL hpx k hk l hkl
  haveI := hL
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  set X := adMat F x with hX
  set Y := pL.map (inclR (F := F) (AF F)) with hY
  have hYX : Y * X = 1 := by
    rw [hX, hY, adMat, ← Matrix.map_mul, hpx]
    simp
  let M : GAd σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun g => (matHom _ σ J g).1
  have hMc : Continuous M := Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous
  have hMmul : ∀ g h, M (g * h) = M g * M h := fun g h => by simp [M]
  have hMinv : ∀ g, M g⁻¹ * M g = 1 := fun g => by simp [M]
  have hM1 : M 1 = 1 := by simp [M]
  let φ : GAd σ J → AF F ⊗[F] E := fun g => (Y * M g * X) 0 0
  have hφc : Continuous φ := by
    have : Continuous fun g => Y * M g * X := (continuous_const.matrix_mul hMc).matrix_mul continuous_const
    exact (continuous_apply 0).comp ((continuous_apply 0).comp this)
  have hdet : ∀ g (c : AF F ⊗[F] E), M g * X = c • X → φ g = c := by
    intro g c h
    simp only [φ, Matrix.mul_assoc, h, Matrix.mul_smul, hYX]
    simp

  have hφ1 : φ 1 = 1 := hdet 1 1 (by rw [hM1, one_smul, Matrix.one_mul])
  have hstep : ∀ g h (c d : AF F ⊗[F] E), M g * X = c • X → M h * X = d • X → M (g * h) * X = (d * c) • X := by
    intro g h c d hg hh
    rw [hMmul, Matrix.mul_assoc, hh, Matrix.mul_smul, hg, smul_smul]
  have hmem : ∀ g, (∃ c : AF F ⊗[F] E, M g * X = c • X) → M g * X = φ g • X := by
    rintro g ⟨c, h⟩
    rw [hdet g c h]; exact h
  let S : Set (GAd σ J) := {g | M g * X = φ g • X ∧ M g⁻¹ * X = φ g⁻¹ • X}
  have hinvφ : ∀ g ∈ S, φ g * φ g⁻¹ = 1 := by
    intro g hg
    have e := hstep g⁻¹ g _ _ hg.2 hg.1
    rw [inv_mul_cancel] at e
    rw [← hdet 1 _ e, hφ1]
  let P : Subgroup (GAd σ J) :=
    { carrier := S
      one_mem' := ⟨by rw [hM1, hφ1, one_smul, Matrix.one_mul], by rw [inv_one, hM1, hφ1, one_smul, Matrix.one_mul]⟩
      mul_mem' := fun {g h} hg hh => ⟨hmem _ ⟨_, hstep _ _ _ _ hg.1 hh.1⟩,
        hmem _ ⟨_, by rw [_root_.mul_inv_rev]; exact hstep _ _ _ _ hh.2 hg.2⟩⟩
      inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩ }
  have hP : IsClosed (P : Set (GAd σ J)) := by
    show IsClosed S
    exact (isClosed_eq (hMc.matrix_mul continuous_const) (hφc.smul continuous_const)).inter
      (isClosed_eq ((hMc.comp continuous_inv).matrix_mul continuous_const) ((hφc.comp continuous_inv).smul continuous_const))
  let u : P →* (AF F ⊗[F] E)ˣ :=
    { toFun := fun p => ⟨φ p, φ (p : GAd σ J)⁻¹, hinvφ p p.2, by rw [mul_comm]; exact hinvφ p p.2⟩
      map_one' := Units.ext (by
        change φ ((1 : P) : GAd σ J) = 1
        rw [OneMemClass.coe_one]; exact hφ1)
      map_mul' := fun p q => Units.ext (by
        change φ ((p * q : P) : GAd σ J) = φ p * φ q
        rw [Subgroup.coe_mul, hdet _ _ (hstep _ _ _ _ p.2.1 q.2.1), mul_comm]) }
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hφc.comp continuous_subtype_val, (hφc.comp continuous_inv).comp continuous_subtype_val⟩
  have hδ : Continuous ((absE F E).comp u) := (GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp hu
  have h2 : M k⁻¹ * X = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X := by
    have e : M k⁻¹ * (M k * X) = X := by rw [← Matrix.mul_assoc, hMinv, Matrix.one_mul]
    have hkl' : M k * X = (l : AF F ⊗[F] E) • X := hkl
    rw [hkl', Matrix.mul_smul] at e
    conv_rhs => rw [← e]
    rw [smul_smul, Units.inv_mul, one_smul]
  have hkP : k ∈ P := ⟨hmem k ⟨_, hkl⟩, hmem _ ⟨_, h2⟩⟩
  have key := GlobalTheory.Doubling.triv_of_isCompact (δ := (absE F E).comp u) (K := levelAll σ J L a) hP hδ
    (GlobalTheory.Doubling.isCompact_levelAll hσ J L a) ⟨k, hkP⟩ hk
  have hul : u ⟨k, hkP⟩ = l := Units.ext (hdet k l hkl)
  change absE F E (u ⟨k, hkP⟩) = 1 at key
  rwa [hul] at key

end GlobalTheory.IwasawaTriv
end

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_adjoint_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  atlas_forward_decl GlobalTheory.IwasawaTriv.absE_eigen_eq_one
end

section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

open Classical in

theorem exists_arch_glue (x : ∀ w : InfinitePlace F, GArch σ J w) (s : Finset (InfinitePlace F)) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
  | insert w s hw ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨embArch σ J w (x w) * q, fun v => by simp [h1 v], fun u => ?_⟩
    by_cases e : u = w
    · subst e; simp [h2 u, hw]
    · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

open Classical in

theorem exists_fin_glue (x : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GLoc σ J v)
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ s then x v else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert v s hv ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J v (x v) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = v
    · subst e; simp [h2 u, hv]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

theorem inv_mul_eq_smul {R : Type} [CommRing R] {m k : ℕ} (M : GL (Fin m) R) (X : Matrix (Fin m) (Fin k) R) (l : Rˣ)
    (h : M.1 * X = l.1 • X) : (M⁻¹).1 * X = (l⁻¹).1 • X := by
  have e : (M⁻¹).1 * (M.1 * X) = X := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h, Matrix.mul_smul] at e
  calc (M⁻¹).1 * X = (l⁻¹).1 • (l.1 • ((M⁻¹).1 * X)) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • X := by rw [e]

omit [NumberField F] [NumberField E] in

theorem first_cols {r : ℕ} (A B : Matrix (Fin n) (Fin (r + 1)) E) :
    cT (σ : E →+* E) (A.submatrix id (fun _ : Fin 1 => 0)) * J * B.submatrix id (fun _ : Fin 1 => 0) =
      (cT (σ : E →+* E) A * J * B).submatrix (fun _ => 0) (fun _ => 0) := by
  ext i j; simp [cT, Matrix.mul_apply]

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem yx_of_xy (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (x y : Matrix (Fin n) (Fin 1) E)
    (h : cT (σ : E →+* E) x * J * y = 1) : cT (σ : E →+* E) y * J * x = 1 := by
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  have key : (cT (σ : E →+* E) y * J * x) 0 0 = σ ((cT (σ : E →+* E) x * J * y) 0 0) := by
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, AlgHom.coe_toRingHom, hs,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hJ.1 l k, hs]; ring
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, key, h]
  simp

end GlobalTheory.IwLine

namespace GlobalTheory.IwLine

open Classical in

theorem iwasawa_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a → (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧ ∃ k ∈ levelAll σ J L a, g = p * k) ∧ ∃ h : GAd σ J → ℝ, ∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l := by
  intro F E _ _ _ _ _ σ hσ hun n J hJ r X Y hW x hx L a hA
  haveI : Submodule.IsLattice E L := hA.lat
  set y : Matrix (Fin n) (Fin 1) E := Y.submatrix id (fun _ => 0) with hy
  have hxx : cT (σ : E →+* E) x * J * x = 0 := by
    rw [hx, first_cols, hW.xx]; rfl
  have hyy : cT (σ : E →+* E) y * J * y = 0 := by
    rw [hy, first_cols, hW.yy]; rfl
  have hxy : cT (σ : E →+* E) x * J * y = 1 := by
    rw [hx, hy, first_cols, hW.xy]; ext i j; simp [Matrix.one_apply, Subsingleton.elim i j]
  have hyx : cT (σ : E →+* E) y * J * x = 1 := yx_of_xy σ J hσ hJ x y hxy
  have loc : ∀ v (g : GLoc σ J v), ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E),
        (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := fun v g =>
    if hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n J hJ x y hxx hyy hxy hyx L hA.lat v hs (hA.dual v) g
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hun n J hJ x y hxx hyx L hA.lat v hs (hA.dual v) g
  have iw : ∀ g : GAd σ J, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
      ∃ k ∈ levelAll σ J L a, g = p * k := by
    intro g
    choose pf kf hkf hf βf hβf using fun v => loc v (proj σ J v g)
    choose pa ka hka ha βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n J hJ x y hxx hyx a hA.maj w (projArch σ J w g)
    have hS := eventually_proj_mem_stabLoc σ J L g
    set S := (Filter.eventually_cofinite.1 hS).toFinset with hSdef
    obtain ⟨qa, qa1, qa2⟩ := exists_arch_glue σ J pa Finset.univ
    obtain ⟨qf, qf1, qf2⟩ := exists_fin_glue σ J pf S
    have pa' : ∀ w, projArch σ J w (qa * qf) = pa w := fun w => by
      rw [map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w)]
    have pf' : ∀ v, proj σ J v (qa * qf) = if v ∈ S then pf v else 1 := fun v => by
      rw [map_mul, qa1 v, qf2 v, one_mul]
    obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n J x (cT (σ : E →+* E) y * J) hyx (qa * qf)
      (fun w => ⟨βa w, by rw [pa' w]; exact hβa w⟩) (fun v => by
        rw [pf' v]
        split_ifs
        · exact ⟨βf v, hβf v⟩
        · exact ⟨1, by simp⟩)
    refine ⟨qa * qf, l, hl, (qa * qf)⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩,
      (mul_inv_cancel_left (qa * qf) g).symm⟩
    · rw [map_mul, map_inv, pf' v]
      split_ifs with h
      · rw [hf v, inv_mul_cancel_left]; exact hkf v
      · rw [inv_one, one_mul]
        by_contra hc
        exact h ((Set.Finite.mem_toFinset _).2 hc)
    · rw [map_mul, map_inv, pa' w, ha w, inv_mul_cancel_left]
      exact hka w
  refine ⟨iw, fun g => (absE F E (iw g).choose_spec.choose : ℝ), fun p l hp k hk => ?_⟩
  obtain ⟨hp', k', hk', e⟩ := (iw (p * k)).choose_spec.choose_spec
  set p' := (iw (p * k)).choose
  set l' := (iw (p * k)).choose_spec.choose
  have hK : p'⁻¹ * p ∈ levelAll σ J L a := by
    have : p'⁻¹ * p = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
    rw [this]; exact mul_mem hk' (inv_mem hk)
  have hm : (matHom _ σ J (p'⁻¹ * p)).1 * adMat F x = (l * l'⁻¹).1 • adMat F x := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, Matrix.mul_smul, map_inv,
      inv_mul_eq_smul _ _ _ hp', smul_smul, Units.val_mul]
  have h1 := GlobalTheory.T.level_subgroup_adjoint_scalar F E σ hσ n J L hA.lat a x (cT (σ : E →+* E) y * J) hyx _ hK _ hm
  rw [map_mul, map_inv, mul_inv_eq_one₀ (GlobalTheory.Doubling.hom_pos _ _).ne'] at h1
  show (absE F E l' : ℝ) = absE F E l
  rw [h1]

end GlobalTheory.IwLine

end
end
