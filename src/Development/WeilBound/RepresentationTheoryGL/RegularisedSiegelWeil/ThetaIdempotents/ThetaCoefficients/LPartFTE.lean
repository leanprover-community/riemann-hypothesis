module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTD

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar GlobalTheory.CompanionTheory.ThetaPoisson

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

theorem mem_gf_of {γ : G D n} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (hu : IsUnit g.det)
    (hU : IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (PositivityTheory.GramSchwartzFunctions.EC.Jm D.host.E n) g)
    (h : mat γ = g.map (incA D)) : γ ∈ GF D n := by
  obtain ⟨γ₀, h0, e⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 g hu hU
  rwa [mat_injective' (e.trans h.symm)] at h0

theorem one_sub_bl' {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 0 = bl hn 0 0 0 1 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem mat_w (hn : r + t = n) (M : Maps D hn) : mat M.w = (wr D.host.E n r).map (incA D) := by
  have hm : (-1 : Matrix (Fin r) (Fin r) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [M.w_mat, wr, eId_eq hn, block_matrix_map, one_sub_bl', block_neg]
  simp [block_map, hm]

theorem mat_emb (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = (wE (bl hn (0 : Matrix (Fin r) (Fin r) D.host.E) 0 0 1)).map (incA D) := by
  have hm : (-1 : Matrix (Fin t) (Fin t) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [M.emb_mat w 0 1 (-1) 0 hw, wE, one_sub_bl, block_neg, block_matrix_map]
  simp [block_map, hm]

theorem mat_emb' (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = blk4 (bl hn 1 0 0 0) (bl hn 0 0 0 1) (bl hn 0 0 0 (-1)) (bl hn 1 0 0 0) :=
  M.emb_mat w 0 1 (-1) 0 hw

theorem adj_Pm (hn : r + t = n) : adj ((Pm D.host.E hn).map (incA D)) = (Pm D.host.E hn)ᵀ.map (incA D) := by
  have h1 : (Pm D.host.E hn).map (incA D) = (1 : Mx D n n).submatrix (πe hn) id := by
    rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [adj, Matrix.transpose_map, h1, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]

def uP (D : D7) (hn : r + t = n) : GL (Fin n) D.host.E := ⟨(Pm D.host.E hn)ᵀ, Pm D.host.E hn, T_mul_Pm hn, Pm_mul_alt hn⟩

theorem mat_gQ {γ : G D n} (hn : r + t = n) (h : mat γ = (blk4 (Pm D.host.E hn)ᵀ 0 0 (Pm D.host.E hn)ᵀ).map (incA D)) :
    mat γ = blk4 ((uP D hn).1.map (incA D)) 0 0 (adj (((uP D hn)⁻¹).1.map (incA D))) := by
  rw [h, block_matrix_map]
  show blk4 _ _ _ _ = blk4 _ _ _ (adj ((Pm D.host.E hn).map (incA D)))
  rw [adj_Pm]
  simp [uP]

def xz {m : ℕ} (X : Mx D m n) : Mx D m (n + n) :=
  Matrix.of fun i k => Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm k)

theorem xPart_xz {m : ℕ} (X : Mx D m n) : xPart (xz X) = X := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem yPart_xz {m : ℕ} (X : Mx D m n) : yPart (xz X) = 0 := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem psi_ip_symm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (x y : Mx D V.rank t) :
    ψ (trA (Matrix.trace (ip V x y))) = ψ (trA (Matrix.trace (ip V y x))) := by
  have hs := pairing_symm (n := t) (isHermND_gram V) ψ x y
  have e : ∀ a b : Mx D V.rank t, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ a b = ψ (trA (Matrix.trace (ip V a b))) :=
    fun a b => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
      rfl
  rw [← e, ← e, hs]

end PositivityTheory.Rg.Rsw.L.LPartFT
