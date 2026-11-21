import Formalism.SharpRestriction.LevelLetterCocycles.DistinctEigenvalueCornerPerturbationOfBlocks

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG

def blockZeroEquiv (r t : ℕ) : Fin r ≃ {a : Fin (r + t) // blkG r t a = 0} where
  toFun a := ⟨Fin.castAdd t a, blkG_castAdd r t a⟩
  invFun y := ⟨(y.1 : ℕ), by
    have h := y.2
    unfold blkG at h
    split_ifs at h with h1
    · exact h1
    · exact absurd h (by simp [Fin.ext_iff])⟩
  left_inv a := by
    ext
    rfl
  right_inv y := by
    apply Subtype.ext
    ext
    rfl

theorem absIrr_block {k G : Type} [Field k] {r t : ℕ} (M : G → Matrix (Fin (r + t)) (Fin (r + t)) k)
    (ρb : G → Matrix (Fin r) (Fin r) k)
    (h : ∀ g a b, M g (Fin.castAdd t a) (Fin.castAdd t b) = ρb g a b)
    (hs : Submodule.span k (Set.range ρb) = ⊤) :
    AbsIrr (fun g => (M g).toSquareBlock (blkG r t) 0) := by
  apply absIrr_of_span
  intro a b
  let L := Matrix.reindexLinearEquiv k k (blockZeroEquiv r t) (blockZeroEquiv r t)
  have hL : ∀ g, L (ρb g) = (M g).toSquareBlock (blkG r t) 0 := by
    intro g
    ext x y
    obtain ⟨x', rfl⟩ := (blockZeroEquiv r t).surjective x
    obtain ⟨y', rfl⟩ := (blockZeroEquiv r t).surjective y
    simp only [L, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply]
    exact (h g x' y').symm
  have h1 : L.symm (Matrix.single a b (1 : k)) ∈ Submodule.span k (Set.range ρb) := by
    rw [hs]
    exact Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := L.toLinearMap) h1
  rw [Submodule.map_span] at h2
  have h3 : L.toLinearMap (L.symm (Matrix.single a b (1 : k))) = Matrix.single a b (1 : k) :=
    L.apply_symm_apply _
  rw [h3] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, (hL g).symm⟩

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

theorem one_le_letterBlockLength (R : Ranks) : 1 ≤ R.t := by
  have h := R.rank_add_five_le
  omega

theorem absIrr_of_res (hN : NormAt N r ρ π)
    (hres : Submodule.span (kk N i)
      (Set.range (mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π))) = ⊤) :
    AbsIrr (fun g => ((repX N r g π).toSquareBlock (blk R) 0).map (IsLocalRing.residue (N.O i))) :=
  absIrr_block (r := R.r) (t := R.t) (fun g => (rO N i r π g).map (IsLocalRing.residue (N.O i)))
    (fun g => mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π) g)
    (fun g a b => congrArg (IsLocalRing.residue (N.O i)) (hN.2.2 g a b)) hres

theorem idem_exists (hN : NormAt N r ρ π)
    (hG1 : ∀ (γ : GE N) (k : ℕ), (fun x : N.X i => ((rO N i r x γ).charpolyRev).coeff k) ∈ N.T i)
    (hres : Submodule.span (kk N i)
      (Set.range (mapM (IsLocalRing.residue (N.O i)) (rhoO N i ρ π))) = ⊤) :
    ∃ eB e₁ : N.X i → MatN N i, IdemHyp (N.O i) (N.T i) (repX N r) π (blk R) eB e₁ := by
  haveI := N.O_complete i
  refine idem (N.O i) (N.X i) (N.T i) (Fin R.nV) (GE N) (repX N r) π R.t (blk R) (chiU N i 1) (epsU N i)
    (primHyp_of N r ρ π hN hG1) (absIrr_of_res N r ρ π hN hres) ?_
  have h1 : Fintype.card {a : Fin (R.r + R.t) // blkG R.r R.t a = 0} = R.r := by
    rw [← Fintype.card_congr (blockZeroEquiv R.r R.t), Fintype.card_fin]
  have h2 : 2 ≤ R.r := by
    have h3 := R.two_le_m
    have h4 := R.m_add_three_le_k
    unfold Ranks.r
    omega
  exact h2.trans (le_of_eq h1.symm)


end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
