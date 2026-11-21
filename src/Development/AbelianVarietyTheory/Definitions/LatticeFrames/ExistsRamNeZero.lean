import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffModel

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}



def HasFrames (p : SplitPt D k) : Prop :=
  ∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k),
    b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b

theorem HasFrames.nonempty {p : SplitPt D k} (h : HasFrames p) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (hn : Fintype.card n = S.rank) : Nonempty (Frame p S n) := by
  let e : n ≃ Fin S.rank := Fintype.equivFinOfCardEq hn
  obtain ⟨β, -⟩ := h S n ((1 : Matrix n n k).submatrix e.symm id) ((1 : Matrix n n k).submatrix id e.symm)
    ((Matrix.submatrix_mul_equiv (1 : Matrix n n k) 1 e.symm (Equiv.refl n) e.symm).trans (by simp))
    (by rw [Matrix.submatrix_mul_equiv (e₂ := e.symm)]; simp)
  exact ⟨β⟩


variable {d : Dat D u} {o : OffDat d k ι}

theorem symplO_kap (H : PinOff o) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (S : HSp D) (x y : WO S d.Lz) :
    symplO _ S (kap (o.τ j h) S x) (kap (o.τ j h) S y) = symplO S d.Lz x y := by
  have := GlobalTheory.LinkKappa.symplO_ofAdj (d.bes j 0 h).L d.Lz S (o.τ j h) (-1) (by simpa using (H.tau j h).1) x y
  simpa [kap] using this


theorem finite_index (H : PinOff o) : Finite ι := Set.finite_univ_iff.1 (o.I.finite_toSet.subset fun i _ => H.all i)



theorem norm_tau (H : PinOff o) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ lam : D.host.E,
    o.τ j h *ᵥ o.ζ₀ = lam • (d.bes j 0 h).ζ ∧
    star lam * lam * (star (d.bes j 0 h).ζ ⬝ᵥ (d.bes j 0 h).L.gram *ᵥ (d.bes j 0 h).ζ) =
      -(D.host.xi0 * star D.host.xi0) * (star o.ζ₀ ⬝ᵥ d.Lz.gram *ᵥ o.ζ₀) := by
  obtain ⟨h1, lam, h2, -⟩ := H.tau j h
  refine ⟨lam, h2, ?_⟩
  have h3 : star (o.τ j h *ᵥ o.ζ₀) ⬝ᵥ (d.bes j 0 h).L.gram *ᵥ (o.τ j h *ᵥ o.ζ₀) =
      star o.ζ₀ ⬝ᵥ ((o.τ j h)ᴴ * ((d.bes j 0 h).L.gram * o.τ j h)) *ᵥ o.ζ₀ := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h4 : (o.τ j h)ᴴ * ((d.bes j 0 h).L.gram * o.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • d.Lz.gram := h1
  rw [h4, h2, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul] at h3
  simpa [mul_assoc] using h3



end GlobalTheory.FinPl.OffModel

end
