import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.ExistsStarMulSelf

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

abbrev Amb (K : Type) [Field K] [NumberField K] (n : ℕ) : Type :=
  EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) : Fin n → ℂ :=
  (Xf v)⁻¹ *ᵥ (fun i => v.embedding (x i))

def mkE (c : InfinitePlace K → Fin n → ℂ) : Amb K n :=
  WithLp.toLp 2 (fun p => if p.2.2 = 0 then (c p.1 p.2.1).re else (c p.1 p.2.1).im)

theorem sum_ulift_finset_fin_two_expand (g : Fin 2 → ℝ) : ∑ k, g k = g 0 + g 1 := Fin.sum_univ_two g

theorem inner_mkE (a c : InfinitePlace K → Fin n → ℂ) :
    inner ℝ (mkE a) (mkE c) = ∑ v, ∑ i, (star (a v i) * c v i).re := by
  simp only [mkE, PiLp.inner_apply, PiLp.toLp_apply, Fintype.sum_prod_type, sum_ulift_finset_fin_two_expand]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

theorem norm_sq_mkE (c : InfinitePlace K → Fin n → ℂ) :
    ‖mkE c‖ ^ 2 = ∑ v, ∑ i, ‖c v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mkE]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

variable [StarRing K]

theorem realize_eq (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x = mkE (fun v => fc Xf v x) := by
  ext p
  have h : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) p.1 x = fun i => p.1.embedding (x i) := by
    funext i
    unfold Formalism.HermitianLatticesTheory.vecAt
    simp
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Formalism.HermitianLatticesTheory.fcoord, mkE, fc, h]

def yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → K) : Amb K n :=
  mkE (fun v => (2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i)))))


variable [IsTotallyComplex K]



end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem nPl_mul_two [IsTotallyComplex K] : Fintype.card (InfinitePlace K) * 2 = finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring


theorem exists_int_smul_mem (X : Submodule (𝓞 K) (Fin n → K))
    (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ X := by
  classical
  have hv : v ∈ Submodule.span K (X : Set (Fin n → K)) := by rw [hX]; trivial
  obtain ⟨m, f, g, hg⟩ := (Submodule.mem_span_set' (R := K)).1 hv
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • f i, hi⟩
  have hr : y • (f i • (g i : Fin n → K)) = r • (g i : Fin n → K) := by
    rw [← algebraMap_smul K r, ← smul_assoc]
    rfl
  rw [hr]
  exact X.smul_mem r (g i).2

variable [StarRing K]

def Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K)) :
    Submodule ℤ (Amb K n) :=
  Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf) X




end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]


theorem norm_sq_realize (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf x‖ ^ 2 = ∑ v, ∑ i, ‖fc Xf v x i‖ ^ 2 := by
  rw [realize_eq, norm_sq_mkE]


end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
