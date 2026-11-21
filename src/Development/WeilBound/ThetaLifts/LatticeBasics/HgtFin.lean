import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaOfFrame
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.MemKFinOfFrameIntegral
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasSatOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood

section
noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.CompanionTheory.IwaDbl.FrameCore GlobalTheory.CompanionTheory.WittOrbit GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.Hgt

section Generic

variable {S : Type} [CommRing S] {c : S →ₐ[ℤ] S} {A : Subring S} {ε : S}

theorem form_star' {l m n : Type} [Fintype m] (hc : ∀ z, c (c z) = z) {H : Matrix m m S} (hH : (H.map c)ᵀ = ε • H)
    (X : Matrix m l S) (Y : Matrix m n S) : ((Xᵀ * H * Y.map c).map c)ᵀ = ε • (Yᵀ * H * X.map c) := by
  rw [map_mul', map_mul', map_map_eq hc, transpose_mul, transpose_mul, hH, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  rfl

theorem exists_partner' {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (hc : ∀ z, c (c z) = z)
    (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w : S} (hw : w ∈ A) (htr : w + c w = 1) {H H' : Matrix m m S}
    (hH : (H.map c)ᵀ = ε • H) (hHA : ∀ i j, H i j ∈ A) (hH'A : ∀ i j, H' i j ∈ A) (hHH : H * H' = 1) {J J' : Matrix n n S}
    (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A) (hJJ : J * J' = 1) {C : Matrix m n S}
    {N : Matrix n m S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A) (hN : N * C = 1) (hC : Cᵀ * H * C.map c = 0) :
    ∃ D : Matrix m n S, (∀ i j, D i j ∈ A) ∧ Cᵀ * H * D.map c = J ∧ Dᵀ * H * C.map c = J ∧ Dᵀ * H * D.map c = 0 := by
  have can : ∀ {X Y : Matrix n n S}, ε • X = ε • Y → X = Y := fun h => (hε.smul_left_cancel).1 h
  obtain ⟨D₁, hD₁A, h1⟩ : ∃ D₁ : Matrix m n S, (∀ i j, D₁ i j ∈ A) ∧ Cᵀ * H * D₁.map c = J := by
    refine ⟨(H' * Nᵀ * J).map c, int_map hs (int_mul (int_mul hH'A fun i j => hNA j i) hJA), ?_⟩
    rw [map_map_eq hc]
    calc Cᵀ * H * (H' * Nᵀ * J) = Cᵀ * (H * H') * Nᵀ * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hHH, Matrix.mul_one, ← transpose_mul, hN, transpose_one, Matrix.one_mul]
  have h2 : D₁ᵀ * H * C.map c = J := can (by rw [← form_star' hc hH, h1, hJ])
  set G := D₁ᵀ * H * D₁.map c with hG
  have hGA : ∀ i j, G i j ∈ A := int_mul (int_mul (fun i j => hD₁A j i) hHA) (int_map hs hD₁A)
  have hGs : (G.map c)ᵀ = ε • G := form_star' hc hH _ _
  obtain ⟨T, hTA, hT⟩ : ∃ T : Matrix n n S, (∀ i j, T i j ∈ A) ∧ J * T.map c = w • G := by
    refine ⟨(w • (J' * G)).map c, int_map hs fun i j => mul_mem hw (int_mul hJ'A hGA i j), ?_⟩
    rw [map_map_eq hc, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hT' : Tᵀ * J = c w • G := can (by
    have := congrArg (fun X : Matrix n n S => (X.map c)ᵀ) hT
    simp only [map_mul', map_map_eq hc, transpose_mul, hJ, Matrix.mul_smul] at this
    rw [this, smul_comm, ← hGs]
    ext i j; simp)
  have hm : (D₁ - C * T).map c = D₁.map c - C.map c * T.map c := by
    rw [← map_mul']; ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have h3 : Cᵀ * H * (D₁ - C * T).map c = J := by
    rw [hm, Matrix.mul_sub, h1, ← Matrix.mul_assoc, hC, Matrix.zero_mul, sub_zero]
  refine ⟨D₁ - C * T, fun i j => sub_mem (hD₁A i j) (int_mul hCA hTA i j), h3, can ?_, ?_⟩
  · rw [← form_star' hc hH, h3, hJ]
  · rw [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc Tᵀ, Matrix.mul_assoc Tᵀ, h3, hT', hm,
      Matrix.mul_sub, ← Matrix.mul_assoc, h2, hT, ← hG, sub_sub, ← add_smul, htr, one_smul, sub_self]

variable {β : Type} [Fintype β] [DecidableEq β]

theorem exists_int_iso (hc : ∀ z, c (c z) = z) (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {J J' : Matrix β β S} (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A)
    (hJJ : J * J' = 1) {C : Matrix (β ⊕ β) β S} {N : Matrix β (β ⊕ β) S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A)
    (hN : N * C = 1) (hC : Cᵀ * dbl J * C.map c = 0) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl J * k.1.map c = dbl J ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      k.1 * diagCols β = C := by
  have hdA : ∀ {X : Matrix β β S}, (∀ i j, X i j ∈ A) → ∀ i j, dbl X i j ∈ A := by
    rintro X hX (i | i) (j | j)
    · exact hX i j
    · exact zero_mem _
    · exact zero_mem _
    · exact neg_mem (hX i j)
  have hJ1 : ∀ i j, c (J j i) = ε * J i j := fun i j => congrFun (congrFun hJ i) j
  have hH : ((dbl J).map c)ᵀ = ε • dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, hJ1]
  have hHH : dbl J * dbl J' = 1 := by
    simp [dbl, fromBlocks_multiply, hJJ]
  obtain ⟨X, hXA, h1, h2, h3⟩ := exists_partner' hc hε hs hw htr hH (hdA hJA) (hdA hJ'A) hHH hJ hJA hJ'A hJJ hCA hNA hN hC
  set K : Matrix (β ⊕ β) (β ⊕ β) S := fromCols (c w₀ • C + X) (w₀ • C - X) with hK
  have hKA : ∀ i j, K i j ∈ A := by
    rintro i (j | j)
    · exact add_mem (mul_mem (hs _ hw) (hCA i j)) (hXA i j)
    · exact sub_mem (mul_mem hw (hCA i j)) (hXA i j)
  have hKm : K.map c = fromCols (w₀ • C.map c + X.map c) (c w₀ • C.map c - X.map c) := by
    ext i (j | j) <;> simp [hK, hc]
  have hU : Kᵀ * dbl J * K.map c = dbl J := by
    rw [hKm, hK, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]
    simp only [transpose_add, transpose_sub, transpose_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, hC, h1, h2, h3, smul_zero, zero_add, add_zero, zero_sub, sub_zero]
    have e : c w₀ = 1 - w₀ := by rw [← htr]; ring
    rw [e]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> module
  have hL : (dbl J' * Kᵀ * dbl J).map c * K = 1 := by
    have : dbl J' * Kᵀ * dbl J * K.map c = 1 := by
      rw [Matrix.mul_assoc (dbl J'), Matrix.mul_assoc (dbl J'), hU, mul_eq_one_comm.mp hHH]
    have := congrArg (fun Y : Matrix (β ⊕ β) (β ⊕ β) S => Y.map c) this
    simp only [map_mul' _ (K.map c), map_map_eq hc] at this
    rw [this]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  refine ⟨⟨K, (dbl J' * Kᵀ * dbl J).map c, mul_eq_one_comm.mp hL, hL⟩, hU, hKA, ?_, ?_⟩
  · exact int_map hs (int_mul (int_mul (hdA hJ'A) fun i j => hKA j i) (hdA hJA))
  · show K * diagCols β = C
    refine (fromCols_mul_fromRows _ _ _ _).trans ?_
    rw [Matrix.mul_one, Matrix.mul_one, add_add_sub_cancel, ← add_smul, add_comm, htr, one_smul]

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (l : S) (H : Matrix β β S) : dbl (l • H) = l • dbl H := by
  simp [dbl, fromBlocks_smul]

theorem lagr_orbit' (hc : ∀ z, c (c z) = z) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {H H' : Matrix β β S} (hH : (H.map c)ᵀ = H) (l : Sˣ) (hHA : ∀ i j, l.1 * H i j ∈ A)
    (hH'A : ∀ i j, H' i j ∈ A) (hHH : (l.1 • H) * H' = 1) (hS : HasSat A β) (y y' : Matrix (β ⊕ β) (β ⊕ β) S)
    (hyy : y' * y = 1) (hy : yᵀ * dbl H * y.map c = dbl H) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl H * k.1.map c = dbl H ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      ∃ t : Matrix β β S, k.1 * diagCols (E := S) β = y * diagCols (E := S) β * t := by
  have hN : ((Matrix.fromCols (1 : Matrix β β S) (0 : Matrix β β S) : Matrix β (β ⊕ β) S) * y') *
      (y * diagCols (E := S) β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc y', hyy, Matrix.one_mul, diagCols, Matrix.fromCols_mul_fromRows]
    simp
  obtain ⟨t, t', D, M, -, h2, h3, h4, h5⟩ := hS _ _ hN
  have hN' : M.toRows₁ * (y * diagCols (E := S) β * t) = 1 := by
    rw [← fromRows_toRows M, fromRows_mul_fromCols, ← fromBlocks_one] at h5
    exact (fromBlocks_inj.mp h5).1
  obtain ⟨κ, k1, k2, k3, k4⟩ := exists_int_iso (ε := c l * (l⁻¹).1) (J := l.1 • H) hc ((l.isUnit.map c).mul (l⁻¹).isUnit) hs hw htr
    (by
      rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]
      conv_rhs => rw [← hH]
      ext i j; simp) hHA hH'A hHH h2 (N := M.toRows₁) (fun i j => h4 _ _) hN'
    (by
      rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul, map_mul', map_mul', Matrix.transpose_mul, Matrix.transpose_mul]
      calc _ = l.1 • (tᵀ * ((diagCols β : Matrix (β ⊕ β) β S)ᵀ * (yᵀ * dbl H * y.map c) *
            (diagCols β : Matrix (β ⊕ β) β S).map c) * t.map c) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hy, diagCols_isotropic, Matrix.mul_zero, Matrix.zero_mul, smul_zero])
  rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul] at k1
  exact ⟨κ, l.isUnit.smul_left_cancel.1 k1, k2, k3, t, k4⟩

end Generic

theorem hasIwasawa_of_frame' {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {n : ℕ}
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (hJ : ∀ i j, σ (J j i) = J i j) (A : Subring (R ⊗[F] E)) (w₀ : R ⊗[F] E)
    (hw : w₀ ∈ A) (htr : w₀ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ w₀ = 1) (hst : ∀ z ∈ A, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ z ∈ A)
    (b : GL (Fin n) (R ⊗[F] E)) (l : (R ⊗[F] E)ˣ) (hint : ∀ i j, l.1 * locGram σ J b i j ∈ A)
    (hinv : ∃ J' : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, J' i j ∈ A) ∧ J' * (l.1 • locGram σ J b) = 1)
    (hS : HasSat A (Fin n)) (K : Subgroup (HA R σ Q))
    (hK : ∀ k : HA R σ Q,
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom R σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) →
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom R σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) → k ∈ K) :
    HasIwasawa σ Q K := by
  intro g
  obtain ⟨J', hJ'A, hJJ'⟩ := hinv
  have hB := gram_blk (R := R) σ hQ b
  set B := blkGL finSumFinEquiv (b, b) with hBdef
  set J₀ := locGram σ J b with hJ₀
  set s := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  let ca : (R ⊗[F] E) →ₐ[ℤ] (R ⊗[F] E) := s.toIntAlgHom
  have hca : ∀ z, ca (ca z) = z := fun z => GlobalTheory.Doubling.sigR_invol hσ z
  have hherm := cT_locGram (R := R) σ hσ hJ b
  rw [← hJ₀] at hherm
  have hg : cT s ((matHom R σ Q g)⁻¹).1 * JR R Q * ((matHom R σ Q g)⁻¹).1 = JR R Q := (g⁻¹).2
  have hx := FrameCore.conj_iso s B hB hg
  set x := B⁻¹ * (matHom R σ Q g)⁻¹ * B with hxdef
  obtain ⟨κ, hκ0, hκ1, hκ2, t, hκ⟩ := lagr_orbit' (c := ca) (H := J₀ᵀ) (H' := J'ᵀ) hca hst hw htr
    (congrArg transpose hherm) l (fun i j => hint j i) (fun i j => hJ'A j i)
    (by rw [← transpose_smul, ← transpose_mul, hJJ', transpose_one]) hS
    (x.1.submatrix finSumFinEquiv finSumFinEquiv) ((x⁻¹).1.submatrix finSumFinEquiv finSumFinEquiv)
    (by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv])
    ((iso_iff s J₀ x.1).1 hx)
  set Y : GL (Fin (n + n)) (R ⊗[F] E) := reGL finSumFinEquiv κ with hYdef
  have hYs : Y.1.submatrix finSumFinEquiv finSumFinEquiv = κ.1 := by
    simp [hYdef, reGL]
  have hY : cT s Y.1 * dblGram finSumFinEquiv J₀ * Y.1 = dblGram finSumFinEquiv J₀ :=
    (iso_iff s J₀ Y.1).2 (by rw [hYs]; exact hκ0)
  have hk : B * Y * B⁻¹ ∈ HR R σ Q := by
    have := FrameCore.conj_iso s B⁻¹ (FrameCore.conj_back s B hB) hY
    rwa [inv_inv] at this
  let kk : HA R σ Q := ⟨B * Y * B⁻¹, hk⟩
  have hkm : matHom R σ Q kk = B * Y * B⁻¹ := rfl
  have h1 : B⁻¹ * matHom R σ Q kk * B = Y := by rw [hkm]; group
  have h2 : B⁻¹ * (matHom R σ Q kk)⁻¹ * B = Y⁻¹ := by rw [hkm]; group
  have hkK : kk ∈ K := hK kk (fun i j => by rw [h1]; exact hκ1 _ _) (fun i j => by rw [h2]; exact hκ2 _ _)
  refine ⟨⟨g * kk, ?_⟩, kk⁻¹, K.inv_mem hkK, (mul_inv_cancel_right g kk).symm⟩
  refine mem_siegelOf.2 ?_
  rw [map_mul, hkm]
  exact keepsDiag_of_frame (matHom R σ Q g) b Y t (by rw [hYs]; exact hκ)

end GlobalTheory.ThK.Dbl.Hgt

end
end

section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl
open PositivityTheory.ThKH.Iwas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

def LocInt (v : Pl F) (z : E) : Prop := ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ o : 𝓞 E, algebraMap F E s * z = o

omit [NumberField E] in
theorem LocInt.mem {z : E} (h : LocInt v z) : inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  obtain ⟨s, hs, o, ho⟩ := h
  exact mem_latLoc_stdLattice.1 (Frames.incl_mem_latLoc (L := stdLattice E 1) hs (x := fun _ => z)
    fun i _ => ⟨o, ho.symm⟩) 0

omit [NumberField F] [NumberField E] in
theorem LocInt.of_mul {z : E} {s : 𝓞 F} (hs : s ∉ v.asIdeal) (h : LocInt v (algebraMap F E s * z)) : LocInt v z := by
  obtain ⟨t, ht, o, ho⟩ := h
  refine ⟨t * s, fun h => (v.isPrime.mem_or_mem h).elim ht hs, o, ?_⟩
  rw [← ho, ← mul_assoc, ← map_mul]; rfl

theorem exists_locGen (v : Pl F) : ∃ δ : E, δ ≠ 0 ∧ InD δ ∧ ∀ z, InD z → LocInt v (δ⁻¹ * z) := by
  set I := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  let e := (LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm
  let L : Submodule (𝓞 E) (Fin 1 → E) := (I : Submodule (𝓞 E) E).map e.toLinearMap
  have hL : ∀ x, x ∈ L ↔ InD (x 0) := fun x => by
    rw [inD_iff]
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h => ⟨x 0, h, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩⟩
  have : L.IsLattice E := ⟨(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _, by
    refine eq_top_iff.2 fun x _ => ?_
    have : x = x 0 • fun _ => (1 : E) := funext fun i => by rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ((inD_iff _).2
      (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))))⟩
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame L v
  obtain ⟨s, hs, hs'⟩ := h1 0
  have hP : P.1 0 0 * (P⁻¹).1 0 0 = 1 := by
    simpa [Matrix.mul_apply] using congrFun (congrFun P.mul_inv 0) 0
  have hs0 : algebraMap F E s ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  refine ⟨algebraMap F E s * P.1 0 0, mul_ne_zero hs0 (left_ne_zero_of_mul_eq_one hP), (hL _).1 hs', fun z hz => ?_⟩
  obtain ⟨t, ht, ht'⟩ := h2 (fun _ => z) ((hL _).2 hz)
  obtain ⟨o, ho⟩ := ht' 0 trivial
  refine LocInt.of_mul hs ⟨t, ht, o, Eq.trans ?_ ho.symm⟩
  rw [mul_inv, mul_assoc, mul_inv_cancel_left₀ hs0, ← eq_inv_of_mul_eq_one_right hP]
  simp [Matrix.mulVec, dotProduct]

omit [NumberField F] in

theorem gram_loc {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    {I : E → Prop} (hI : ∀ z, I z → ∀ b : 𝓞 E, I (z * b)) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, I (form σ J y x))
    {δ : E} (hδ : I δ) (hmax : ∀ z, I z → LocInt v (δ⁻¹ * z))
    (P : GL (Fin n) E) (h1 : ∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • (fun i => P.1 i j) ∈ L)
    (h2 : ∀ x ∈ L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n) :
    ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
  classical
  set G := P.1ᵀ * J * P.1.map σ with hG
  have hGu : IsUnit G.det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have a1 : IsUnit P.1.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
    have a2 : (P.1.map σ).det = σ P.1.det := (RingHom.map_det (σ : E →+* E) _).symm
    rw [a2]
    exact (a1.mul hJ.isUnit).mul (a1.map σ)
  have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
  refine ⟨G⁻¹, hG', fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h1 j
    have e : ∀ (t : E) (k : Fin n), t • (fun i => P.1 i k) = P.1 *ᵥ Pi.single k t := fun t k => by
      ext l; simp [mul_comm]
    have := hmax _ ((hd _).1 ha' _ hb')
    rw [e, e, form_mulVec, ← hG, show (fun l => σ (Pi.single (M := fun _ => E) j (algebraMap F E b) l)) =
      Pi.single j (algebraMap F E b) from funext fun l => by
        by_cases el : l = j
        · subst el; simp
        · simp [el]] at this
    rw [single_dotProduct, Matrix.mulVec_single] at this
    change LocInt v (δ⁻¹ * (algebraMap F E a * (G i j * algebraMap F E b))) at this
    refine LocInt.of_mul hb (LocInt.of_mul ha ?_)
    convert this using 1
    ring
  · obtain ⟨S, hS⟩ := hL
    choose! f hf hf' using h2
    have hmemS : ∀ x ∈ S, x ∈ L := fun x hx => hS ▸ Submodule.subset_span hx
    have := v.isPrime
    let t : 𝓞 F := ∏ x ∈ S, f x
    have ht : t ∉ v.asIdeal := by
      intro hmem
      obtain ⟨x, hx, hx'⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hf x (hmemS x hx) hx'
    have ht' : ∀ x ∈ L, algebraMap F E t • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n := fun x hx => by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have e : t = (∏ y ∈ S.erase x, f y) * f x := (Finset.prod_erase_mul _ _ hx).symm
        have e' : algebraMap F E t = algebraMap F E (∏ y ∈ S.erase x, f y : 𝓞 F) * algebraMap F E (f x) := by
          rw [e, ← map_mul]; rfl
        rw [e', mul_smul]
        exact (stdLattice E n).smul_mem (algebraMap (𝓞 F) (𝓞 E) (∏ y ∈ S.erase x, f y)) (hf' x (hmemS x hx))
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact (stdLattice E n).smul_mem a hx
    let u : Fin n → E := (algebraMap F E t * δ) • G⁻¹ i
    have hy : P.1 *ᵥ u ∈ L := (hd _).2 fun x hx => by
      obtain ⟨o, ho⟩ := ht' x hx i trivial
      have ex : x = P.1 *ᵥ ((P⁻¹).1 *ᵥ x) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e : form σ J (P.1 *ᵥ u) x = δ * ((RingOfIntegers.mapRingHom (σ : E →+* E) o : 𝓞 E) : E) := by
        rw [ex, form_mulVec, ← hG, Matrix.dotProduct_mulVec, Matrix.smul_vecMul,
          show G⁻¹ i ᵥ* G = Pi.single i 1 from funext fun l => by
            rw [← Matrix.mul_apply_eq_vecMul, hG', Matrix.one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl,
          smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
        change _ = δ * σ (Algebra.linearMap (𝓞 E) E o)
        rw [ho, Pi.smul_apply, smul_eq_mul, map_mul, σ.commutes]
        ring
      rw [e]
      exact hI _ hδ _
    obtain ⟨o, ho⟩ := hf' _ hy j trivial
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at ho
    refine LocInt.of_mul ht ⟨f _, hf _ hy, o, Eq.trans ?_ ho.symm⟩
    simp [u, mul_assoc]

theorem hasSat_good {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : HasSat (intLoc F E v) (Fin n) := by
  have e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u),
      a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K :=
    fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hc := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · refine hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool)
      (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v))
      (fun y z h => split_ext hc τ (h true) (h false))
      (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun i => ?_⟩) _ (fun y => ?_) _
    · cases i
      · exact splitProj_comp_symm hc τ _
      · exact splitProj_symm hc τ _
    · rw [mem_intLoc_iff_split hc τ, Bool.forall_bool]
      simp only [cond_false, cond_true, e]
      exact and_comm
  · have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
    refine hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h)
      (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _
    · obtain ⟨y, hy⟩ := (InertChart.toCompl_bijective hw h).2 (f ())
      exact ⟨y, fun _ => hy⟩
    · rw [InertChart.mem_intLoc_iff hw h]
      exact ⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩

theorem hasIwasawa_fin' {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) {ξ : E} (hξ : ξ ≠ 0) (hh : ∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) (v : Pl F) :
    HasIwasawa σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) (GlobalTheory.Doubling.KFin σ _ Y.L v) := by
  have hσ := cm_conj_conj hB.cm
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  obtain ⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
    rcases hY with h | h
    · exact ⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
        isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩
    · obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
      exact ⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  let ι := inclR (F := F) (E := E) (Fv F v)
  let l : (Fv F v ⊗[F] E)ˣ := Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹
  have e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι := by
    have e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι := by
      rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul, ← Matrix.smul_mul,
        ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e1]
    ext i j
    change ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)
    rw [← map_mul]; congr 1; field_simp
  refine hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_
    (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩
    (hasSat_good hB v) _ fun k => mem_KFin_of_frame_integral σ _ (Frames.frame_of_rational P h1 h2) k
  · change (1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1
    rw [← TensorProduct.tmul_add, ht]
    rfl
  · change (l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _
    rw [e]
    exact (b1 j i).mem
  · rw [e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, ← Matrix.transpose_mul,
      mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ThK.Dbl.Hgt

end
end
