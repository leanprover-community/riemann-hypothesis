import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchACompCoordEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCompactUnderWittChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.LeviChart
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : ∃ a b c d, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

theorem submatrix_fromBlocks_levi {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [blk4]

theorem diag_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z Z' a b c d : Matrix (Fin n) (Fin n) R} (hZ : Z' * Z = 1)
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d) (hU : KeepsDiag finSumFinEquiv U) :
    c = 0 ∧ a = leviMat finSumFinEquiv U := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := blockMatrixTwoByTwoFin_injective h
  simp only [KeepsDiag, leviMat, submatrix_fromBlocks_levi, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at hU ⊢
  simp only [mul_one, one_mul, neg_mul] at h1 h3
  have h4 : Z * c = 0 := h2 _ (by
    have : a + Z * c = a + -(Z * c) := by rw [← h1, ← h3, hU]
    exact eq_neg_iff_add_eq_zero.1 (add_left_cancel this))
  refine ⟨by rw [← one_mul c, ← hZ, mul_assoc, h4, mul_zero], by rw [h1, h4, add_zero]⟩

theorem anti_blocks {R : Type} [CommRing R] {n : ℕ} (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    {U : Matrix (Fin (n + n)) (Fin (n + n)) R} {Z a b c d : Matrix (Fin n) (Fin n) R}
    (h : U * blk4 1 Z 1 (-Z) = blk4 1 Z 1 (-Z) * blk4 a b c d)
    (hU : ∀ w ∈ antiSub R finSumFinEquiv, U *ᵥ w ∈ antiSub R finSumFinEquiv) : b = 0 := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq U
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h
  obtain ⟨-, h1, -, h3⟩ := blockMatrixTwoByTwoFin_injective h
  have h4 : p * Z + q * -Z = -(r * Z + s * -Z) := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have := hU _ ((pairVec_mem_antiSub finSumFinEquiv).2
      (neg_neg _).symm : pairVec finSumFinEquiv (Z *ᵥ Pi.single j 1) (-(Z *ᵥ Pi.single j 1)) ∈ _)
    rw [mulVec_pairVec, pairVec_mem_antiSub, submatrix_fromBlocks_levi] at this
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, ← Matrix.neg_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.add_mulVec] at this
    exact this
  rw [h1, h3] at h4
  simp only [one_mul, neg_mul] at h4
  refine h2 _ ?_
  have := eq_neg_iff_add_eq_zero.1 h4
  rw [← this]; abel

theorem inv_cancel {M : Type} [Monoid M] {x y d : M} (h1 : y * x = 1) (h2 : x * d = 1) : d = y := by
  rw [← one_mul d, ← h1, mul_assoc, h2, mul_one]

variable {D : D7} {n : ℕ}

theorem adj_inv_mul (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_mul_eq_one {g : G D n} {a b d : Mx D n n} (hg : mat g = blk4 a b 0 d) : adj a * d = 1 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_zero, mul_zero, zero_mul, mul_one, add_zero, zero_add] at h
  exact (blockMatrixTwoByTwoFin_injective h).2.1

theorem rat_witt {J : Matrix (Fin n) (Fin n) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hT : IsWittBasis D.sp.cm.sig J 1 T) :
    ∃ Z Z' : Mx D n n, Z' * Z = 1 ∧ (rat T.1 : Mx D (n + n) (n + n)) = blk4 1 Z 1 (-Z) := by
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  exact ⟨rat Z, _, h2, by rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]⟩

theorem levi_form {M : Mx D (n + n) (n + n)} {x b d : Mx D n n} (a : GL (Fin n) (AE D)) (e : x = a.1)
    (h : M = blk4 x b 0 d) (hb : b = 0) (hd : adj x * d = 1) : M = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  subst e
  rw [h, hb, inv_cancel (adj_inv_mul a) hd]

section
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* G D n}
  {J : Matrix (Fin n) (Fin n) D.host.E}

theorem siegel_blocks (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hk : KeepsDiag finSumFinEquiv (umat g)) : ∃ b d : Mx D n n,
      mat (κ g) = blk4 (leviMat finSumFinEquiv (umat g)) b 0 d ∧ adj (leviMat finSumFinEquiv (umat g)) * d = 1 ∧
      ((∀ w ∈ antiSub (AE D) finSumFinEquiv, umat g *ᵥ w ∈ antiSub (AE D) finSumFinEquiv) → b = 0) := by
  obtain ⟨Z, Z', hZ, hT⟩ := rat_witt hT
  obtain ⟨a, b, c, d, h⟩ := exists_blockMatrixTwoByTwoFin_eq (mat (κ g))
  have h1 := hκ.mul_eq g
  rw [hT, h] at h1
  have h2 : ∀ z : Mx D n n, z + z = 0 → z = 0 := fun z hz => eq_zero_of_add_self hz
  obtain ⟨hc, ha⟩ := diag_blocks (R := AE D) h2 hZ h1 hk
  have h3 := anti_blocks (R := AE D) h2 h1
  rw [hc, ha] at h
  exact ⟨b, d, h, adj_mul_eq_one h, h3⟩

theorem levi_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hp : g ∈ leviSubOf finSumFinEquiv (uinc D J₂)) (a : GL (Fin n) (AE D))
    (e : leviMat finSumFinEquiv (umat g) = a.1) : mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨b, d, h, hd, hb⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hp1)
  exact levi_form a e h (hb fun w hw => (hp2 w).1 hw) hd

theorem unip_chart (hκ : IsChartW T κ) (hT : IsWittBasis D.sp.cm.sig J 1 T) {g : UD D J₂}
    (hg : g ∈ unipOf finSumFinEquiv (uinc D J₂)) : ∃ β : Mx D n n, mat (κ g) = blk4 1 β 0 1 := by
  obtain ⟨hg1, hg2⟩ := mem_unipOf.1 hg
  obtain ⟨b, d, h, hd, -⟩ := siegel_blocks hκ hT (g := g) (mem_siegelOf.1 hg1)
  have e : leviMat finSumFinEquiv (umat g) = 1 := hg2
  rw [e] at h hd
  rw [adj_one, one_mul] at hd
  exact ⟨b, by rw [h, hd]⟩

end

theorem levi_unip_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ p : siegelOf finSumFinEquiv (uinc D J₂), (p : UD D J₂) ∈ leviSubOf finSumFinEquiv (uinc D J₂) → GlobalTheory.StdUnn.mat (κ p) = GlobalTheory.StdUnn.blk4 (leviOf finSumFinEquiv (uinc D J₂) p).1 0 0 (adj ((leviOf finSumFinEquiv (uinc D J₂) p)⁻¹).1)) ∧ ∀ b ∈ unipOf finSumFinEquiv (uinc D J₂), ∃ β : Mx D n n, GlobalTheory.StdUnn.mat (κ b) = GlobalTheory.StdUnn.blk4 1 β 0 1 :=
  fun _ _ _ _ _ hκ _ hT => ⟨fun p hp => levi_chart hκ hT hp _ (val_leviOf p).symm, fun _ hg => unip_chart hκ hT hg⟩

end GlobalTheory.SWLink.LeviChart
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_chart_block_diagonal_adjoint : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ p : siegelOf finSumFinEquiv (uinc D J₂), (p : UD D J₂) ∈ leviSubOf finSumFinEquiv (uinc D J₂) → GlobalTheory.StdUnn.mat (κ p) = GlobalTheory.StdUnn.blk4 (leviOf finSumFinEquiv (uinc D J₂) p).1 0 0 (adj ((leviOf finSumFinEquiv (uinc D J₂) p)⁻¹).1)) ∧ ∀ b ∈ unipOf finSumFinEquiv (uinc D J₂), ∃ β : Mx D n n, GlobalTheory.StdUnn.mat (κ b) = GlobalTheory.StdUnn.blk4 1 β 0 1 := by
  atlas_forward_decl GlobalTheory.SWLink.LeviChart.levi_unip_chart
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem exists_pt_anti (hT : IsWittBasis D.sp.cm.sig J 1 T) {m : ℕ} {u : Mx D m (n + n)}
    (hu : ∀ i, u i ∈ antiSub (AE D) finSumFinEquiv) : ∃ x, u = pt T 0 x := by
  obtain ⟨q, x, rfl⟩ := exists_pt T u
  rw [(pt_anti_iff hT q x).1 hu]
  exact ⟨x, rfl⟩

theorem IsTrans.right (hom : IsTrans ε ι κ ω om) (g : UD D J₂) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (h : φ ∘ coord ε = Φ.1)
    (x : Mx D V.rank n) : om (1, g) φ (coord ε x) = (ω (κ g) Φ).1 x := by
  rw [hom.2 1 g φ hφ Φ h, map_one, inv_one, mt_one, Matrix.one_mul]

theorem invOf_two_mul (z : AE D) : ⅟(2 : AF D.host.F) * StdUnn.trA z = StdUnn.halfTr z := by
  rw [StdUnn.halfTr]
  congr 1
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem mat_inv_weyl {w : StdUnn.G D n} (hw : StdUnn.mat w = StdUnn.blk4 0 1 (-1) 0) :
    StdUnn.mat w⁻¹ = StdUnn.blk4 0 (-1) 1 0 := by
  have h1 : StdUnn.mat w⁻¹ * StdUnn.mat w = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, StdUnn.LeftInvSect.mat_one]
  have h2 : (StdUnn.blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [StdUnn.Model.submatrix_fromBlocks_mul, ← StdUnn.Model.block_matrix_one]
    simp only [mul_zero, zero_mul, mul_one, add_zero, zero_add, mul_neg, neg_zero, neg_neg]
  rw [← Matrix.mul_one (StdUnn.mat w⁻¹), ← h2, ← hw, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem zmul {a b c : ℕ} (y : Mx D b c) : ((0 : Mx D a b) ⬝ y : Mx D a c) = 0 := Matrix.zero_mul y

theorem mulz {a b c : ℕ} (y : Mx D a b) : (y ⬝ (0 : Mx D b c) : Mx D a c) = 0 := Matrix.mul_zero y

theorem mulo {a b : ℕ} (y : Mx D a b) : (y ⬝ (1 : Mx D b b) : Mx D a b) = y := Matrix.mul_one y

theorem formula_lin (hθ : IsInfFam θ) (hι : IsConjV V ι) (hco : IsCoord V T ε co) (hom : IsTrans ε ι κ ω om)
    (h : UD D (-V.gram)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (h, 1) φ (co.e (pt T 0 x)).1 = φ (co.e (umat h⁻¹ ⬝ pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [mul_pt, (hco _ _).1, (hco _ _).1, hom.2 h 1 φ hφ ⟨_, hS⟩ rfl, map_one, map_one, ← map_inv, hι]
  rfl

theorem formula_levi (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {p : UD D J₂} {a : GL (Fin n) (AE D)}
    (h1 : StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1))
    (h2 : StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1)) {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, p) φ (co.e (pt T 0 x)).1 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) * φ (co.e (pt T 0 x ⬝ (umat p⁻¹)ᵀ)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  rw [hκ.pt_mul h2, (hco _ _).1, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.levi _ _ h1, zmul, zero_add, adj_adj]
  rfl

theorem formula_unip (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    (hom : IsTrans ε ι κ ω om) {b : UD D J₂} {β : Mx D n n} (hβ : StdUnn.mat (κ b) = StdUnn.blk4 1 β 0 1)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, b) φ (co.e (pt T 0 x)).1 =
      ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂)
        (pt T 0 x ⬝ (umat b)ᵀ) (pt T 0 x)) * φ (co.e (pt T 0 x)).1 := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have e1 : StdUnn.inner V (x ⬝ adj β : Mx D V.rank n) x = β ⬝ StdUnn.inner V x x := by
    rw [StdUnn.inner, StdUnn.inner, adj_mul, adj_adj, Matrix.mul_assoc]
  have e2 : ∀ y, StdUnn.inner V y (0 : Mx D V.rank n) = 0 := fun y => by rw [StdUnn.inner, mulz, mulz]
  rw [hκ.pt_mul hβ, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.unip _ _ hβ, symp_pt V hG, e2, zmul, zero_add, e1,
    Matrix.trace_zero]
  have e3 : StdUnn.trA (0 : AE D) = 0 := map_zero _
  rw [e3, sub_zero, invOf_two_mul]
  rfl

theorem formula_weyl (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hκ : IsChartW T κ) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) {w : UD D J₂} (hw : StdUnn.mat (κ w) = StdUnn.blk4 0 1 (-1) 0)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (x : Mx D V.rank n) :
    om (1, w) φ (co.e (pt T 0 x)).1 = 1 * ∫ y, φ y * ψ (y ⬝ᵥ (co.e (pt T 0 x ⬝ (umat w⁻¹)ᵀ)).2) ∂μ' := by
  have hS := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  have h2 : StdUnn.mat (κ w⁻¹) = StdUnn.blk4 0 (-1) 1 0 := by rw [map_inv]; exact mat_inv_weyl hw
  have e0 : ((0 : Mx D V.rank n) ⬝ adj (0 : Mx D n n) + x ⬝ adj (-1 : Mx D n n) : Mx D V.rank n) = -x := by
    rw [zmul, zero_add, adj_neg, adj_one, Matrix.mul_neg, mulo]
  rw [hκ.pt_mul h2, e0, (hco _ _).1, hom.right _ hφ ⟨_, hS⟩ rfl, hω.weyl _ hw, one_mul, hμ]
  refine integral_congr_ae (.of_forall fun y => ?_)
  have e1 : StdUnn.inner V y (-x) = -StdUnn.inner V y x := by
    rw [StdUnn.inner, StdUnn.inner, Matrix.mul_neg, Matrix.mul_neg]
  have e3 : ∀ z : AE D, StdUnn.trA (-z) = -StdUnn.trA z := fun z => map_neg _ z
  beta_reduce
  rw [(hco _ _).2, e1, Matrix.trace_neg, e3, neg_neg, trA_inner_comm]
  rfl

theorem levi_pair (hT : IsWittBasis D.sp.cm.sig J 1 T) (hκ : IsChartW T κ) {p : UD D J₂}
    (hs : p ∈ siegelOf finSumFinEquiv (uinc D J₂)) (hp : p ∈ leviSubOf finSumFinEquiv (uinc D J₂)) :
    ∃ a : GL (Fin n) (AE D), aOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = Matrix.GeneralLinearGroup.det a ∧
      StdUnn.mat (κ p) = StdUnn.blk4 a.1 0 0 (adj (a⁻¹).1) ∧ StdUnn.mat (κ p⁻¹) = StdUnn.blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).1 ⟨p, hs⟩ hp
  refine ⟨leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩, rfl, h1, ?_⟩
  generalize leviOf finSumFinEquiv (uinc D J₂) ⟨p, hs⟩ = a at h1 ⊢
  have h2 : StdUnn.mat (κ p⁻¹) * StdUnn.mat (κ p) = 1 := by
    rw [← StdUnn.LeftInvSect.mat_mul, ← map_mul, inv_mul_cancel, map_one, StdUnn.LeftInvSect.mat_one]
  rw [← Matrix.mul_one (StdUnn.mat (κ p⁻¹)), ← StdUnn.LeftInvSect.levi_mul_inv a, ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem formulas (hθ : IsInfFam θ) (hω : StdUnn.IsWeilSch ψ χ θ V μ ω) (hT : IsWittBasis D.sp.cm.sig J 1 T)
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = StdUnn.Jst D n) (hκ : IsChartW T κ) (hι : IsConjV V ι) (hco : IsCoord V T ε co)
    [MeasurableSpace (Fin V.rank × Fin n × Fin d → AF D.host.F)] {μ' : Measure (Fin V.rank × Fin n × Fin d → AF D.host.F)}
    (hμ : ∀ f : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ)
    (hom : IsTrans ε ι κ ω om) : IsWeilFormulas D.sp.cm.sig ψ χ T co μ' om := by
  refine ⟨hom.1, ?_, ?_, ?_, ?_⟩
  · intro h φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_lin hθ hι hco hom h hφ x
  · rintro ⟨p, hs⟩ hp φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨a, ha, h1, h2⟩ := levi_pair hT hκ hs hp
    rw [ha]
    exact formula_levi hθ hω hκ hco hom h1 h2 hφ x
  · intro b hb φ hφ u hu
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.levi_chart_block_diagonal_adjoint D n J₂ T κ hκ J hT).2 b hb
    exact formula_unip hθ hω hG hκ hco hom hβ hφ x
  · intro w hw
    refine ⟨1, 1, one_pos, one_pow _, fun φ hφ u hu => ?_⟩
    obtain ⟨x, rfl⟩ := exists_pt_anti hT hu
    exact formula_weyl hθ hω hκ hco hμ hom ((hκ w).trans hw) hφ x

end GlobalTheory.SWLink

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_witt_basis_compact_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (l : E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E), l ≠ 0 → J.det ≠ 0 → J₂ = dblGram finSumFinEquiv J → ∃ (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)), IsWittBasis σ J l T ∧ IsStdK σ T K ∧ IsCompact (K : Set (UA σ J₂)) := by
  first | exact @GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK | exact GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK | (intros; apply GlobalTheory.SWLit.WittStd.exists_wittBasis_stdK <;> assumption)
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkChart

theorem exists_conj {Γ : Type} [Group Γ] (H K : Subgroup Γ) (t : Γ) (h : ∀ g, g ∈ H ↔ t⁻¹ * g * t ∈ K) :
    ∃ κ : H ≃* K, ∀ g, (κ g).1 = t⁻¹ * g.1 * t :=
  ⟨{ toFun := fun g => ⟨t⁻¹ * g.1 * t, (h _).1 g.2⟩
     invFun := fun k => ⟨t * k.1 * t⁻¹, (h _).2 (by simpa [mul_assoc] using k.2)⟩
     left_inv := fun g => Subtype.ext (by simp [mul_assoc])
     right_inv := fun g => Subtype.ext (by simp [mul_assoc])
     map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl⟩

theorem gram_iff {R : Type} [CommRing R] {k : ℕ} (g g' S S' C C' J : Matrix (Fin k) (Fin k) R)
    (h1 : S * S' = 1) (h2 : C * C' = 1) :
    gᵀ * J * g' = J ↔ (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * J * C := by
  have h3 : S'ᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e : (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * (gᵀ * J * g') * C := by
    calc _ = Sᵀ * (gᵀ * (S'ᵀ * Sᵀ) * J * (C * C') * g') * C := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.mul_one]
  rw [e]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have f : ∀ X : Matrix (Fin k) (Fin k) R, S'ᵀ * (Sᵀ * X * C) * C' = X := fun X => by
    calc _ = (S'ᵀ * Sᵀ) * X * (C * C') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.one_mul]
  rw [← f (gᵀ * J * g'), h, f]

theorem conj_iff {D : D7} {k : ℕ} (x W : Mx D k k) (hW : cj W = W) :
    xᵀ * W * cj x = W ↔ adj x * W * x = W := by
  constructor
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, cj_cj, hW, cj_transpose, ← adj_eq] at this
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, hW, adj_eq, cj_transpose, cj_cj] at this

theorem cj_Jst (D : D7) (n : ℕ) :
    cj (rat (StdUnn.Jst D n) : Mx D (n + n) (n + n)) = rat (StdUnn.Jst D n) := by
  rw [rat_Jst, cj, block_matrix_map]
  change StdUnn.blk4 (cj 0) (cj 1) (cj (-1)) (cj 0) = _
  rw [cj_neg, cj_zero, cj_one]

theorem mem_UG_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ (g.1 : Mx D k k)ᵀ * rat J * cj g.1 = rat J := by
  rw [← map_cAl, ← incM_eq]
  exact Iff.rfl

theorem mem_HR_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig J ↔ adj (g.1 : Mx D k k) * rat J * g.1 = rat J := Iff.rfl

theorem mat_iff {D : D7} {k : ℕ} (g S S' J W : Mx D k k) (h1 : S * S' = 1) (hG : Sᵀ * J * cj S = W) (hW : cj W = W) :
    gᵀ * J * cj g = J ↔ adj (S' * g * S) * W * (S' * g * S) = W := by
  have hc : cj S * cj S' = 1 := by rw [← cj_mul, h1, cj_one]
  rw [← conj_iff _ _ hW, cj_mul, cj_mul, ← hG]
  exact gram_iff g (cj g) S S' (cj S) (cj S') J h1 hc

theorem mem_iff {D : D7} {k : ℕ} (J W : Matrix (Fin k) (Fin k) D.host.E) (t : GL (Fin k) (AE D))
    (hG : (t.1 : Mx D k k)ᵀ * rat J * cj t.1 = rat W) (hW : cj (rat W : Mx D k k) = rat W) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ t⁻¹ * g * t ∈ HR (AF D.host.F) D.sp.cm.sig W := by
  rw [mem_UG_iff, mem_HR_iff, Units.val_mul, Units.val_mul]
  exact mat_iff g.1 t.1 (t⁻¹).1 _ _ t.mul_inv hG hW

theorem exists_isChartW : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  intro D n J₂ T hG
  have hW : (rat T.1 : Mx D (n + n) (n + n))ᵀ * rat J₂ * cj (rat T.1) = rat (StdUnn.Jst D n) := by
    rw [← hG, rat_mul, rat_mul, cj_rat]; rfl
  obtain ⟨κ, hκ⟩ := exists_conj _ _ _
    (mem_iff J₂ (StdUnn.Jst D n) ⟨rat T.1, rat (T⁻¹).1, rat_mul_inv T, rat_inv_mul T⟩ hW (cj_Jst D n))
  refine ⟨κ, fun g => ?_⟩
  exact congrArg Units.val (hκ g)

end GlobalTheory.SWLinkChart

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_change_basis_unitary_iso : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  atlas_forward_decl GlobalTheory.SWLinkChart.exists_isChartW
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Sieg

def blkC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b c d, M = StdUnn.blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold StdUnn.blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

theorem submatrix_sum_equiv_fromBlocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (StdUnn.blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [StdUnn.blk4]

theorem key {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) (Z Z' : Matrix (Fin n) (Fin n) R)
    (hZ : Z' * Z = 1) (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    (h : M * StdUnn.blk4 1 Z 1 (-Z) = StdUnn.blk4 1 Z 1 (-Z) * N) :
    (KeepsDiag finSumFinEquiv M ↔ blkC N = 0) ∧ (blkC N = 0 → StdUnn.blkA N = leviMat finSumFinEquiv M) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq N
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq M
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul] at h1 h3
  simp only [KeepsDiag, leviMat, blkC, StdUnn.blkA, submatrix_sum_equiv_fromBlocks, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, h1, h3]
  refine ⟨⟨fun h4 => ?_, fun h4 => by simp [h4]⟩, fun h4 => by simp [h4]⟩
  have h5 : Z * c = 0 := h2 _ (neg_eq_iff_add_eq_zero.1 (add_left_cancel h4))
  rw [← Matrix.one_mul c, ← hZ, Matrix.mul_assoc, h5, Matrix.mul_zero]

theorem mulVec_upper {R : Type} [CommRing R] {n : ℕ} {N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hN : blkC N = 0)
    (x : Fin (n + n) → R) (hx : ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0) (i : Fin n) :
    (N *ᵥ x) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := by
  have h : ∀ j : Fin n, N (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = 0 :=
    fun j => congrFun (congrFun hN i) j
  simp only [Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [h, hx, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

variable {D : D7} {n : ℕ}

theorem mem_upperHalf {x : Fin (n + n) → AE D} :
    x ∈ StdUnn.upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 :=
  funext_iff

theorem mem_siegelParabolic_of {g : StdUnn.G D n} (h : blkC (StdUnn.mat g) = 0) (h' : blkC (StdUnn.mat g⁻¹) = 0) :
    g ∈ StdUnn.P D n := by
  refine fun x => ⟨fun hx => mem_upperHalf.2 (mulVec_upper h x (mem_upperHalf.1 hx)), fun hx => ?_⟩
  have : (StdUnn.mat g⁻¹).mulVec ((StdUnn.mat g).mulVec x) ∈ StdUnn.upperHalf D n :=
    mem_upperHalf.2 (mulVec_upper h' _ (mem_upperHalf.1 hx))
  rwa [Matrix.mulVec_mulVec, show StdUnn.mat g⁻¹ * StdUnn.mat g = StdUnn.mat (g⁻¹ * g) from rfl, inv_mul_cancel,
    show StdUnn.mat (1 : StdUnn.G D n) = 1 from rfl, Matrix.one_mulVec] at this

theorem blkC_of_mem_P {g : StdUnn.G D n} (h : g ∈ StdUnn.P D n) : blkC (StdUnn.mat g) = 0 := by
  funext i j
  exact StdUnn.Model.lower_eq_zero h i j

theorem siegel_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ GlobalTheory.StdUnn.P D n) ∧ ∀ p : siegelOf finSumFinEquiv (uinc D J₂), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1 := by
  intro D n J₂ T κ hκ J hT
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  have hm : (rat T.1 : Mx D (n + n) (n + n)) = StdUnn.blk4 1 (rat Z) 1 (-rat Z) := by
    rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]
  have hk : ∀ g : UD D J₂, (KeepsDiag finSumFinEquiv (umat g) ↔ blkC (StdUnn.mat (κ g)) = 0) ∧
      (blkC (StdUnn.mat (κ g)) = 0 → StdUnn.blkA (StdUnn.mat (κ g)) = leviMat finSumFinEquiv (umat g)) := fun g =>
    key _ _ _ _ h2 (fun _ => eq_zero_of_add_self) (by rw [← hm]; exact hκ.mul_eq g)
  have hs : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ blkC (StdUnn.mat (κ g)) = 0 := fun g =>
    mem_siegelOf.trans (hk g).1
  refine ⟨fun g => ⟨fun hg => mem_siegelParabolic_of ((hs g).1 hg) ?_, fun hg => (hs g).2 (blkC_of_mem_P hg)⟩,
    fun p => (hk p).2 ((hs p).1 p.2)⟩
  rw [← map_inv]
  exact (hs _).1 (inv_mem hg)

end GlobalTheory.SWLink.Sieg

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_parabolic_chart_levi_block : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ GlobalTheory.StdUnn.P D n) ∧ ∀ p : siegelOf finSumFinEquiv (uinc D J₂), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1 := by
  atlas_forward_decl GlobalTheory.SWLink.Sieg.siegel_chart
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_under_witt_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ K : Subgroup (UD D J₂), IsStdK D.sp.cm.sig T K → ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ GlobalTheory.StdUnn.K D n := by
  first | exact @GlobalTheory.SWLink.stdK_iff | exact GlobalTheory.SWLink.stdK_iff | (intros; apply GlobalTheory.SWLink.stdK_iff <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

noncomputable section

namespace GlobalTheory.SWLink.Conj

variable {D : D7}

def cjG (D : D7) (k : ℕ) : GL (Fin k) (AE D) →* GL (Fin k) (AE D) := Matrix.GeneralLinearGroup.map (cA D)


theorem cjG_cjG {k : ℕ} (g : GL (Fin k) (AE D)) : cjG D k (cjG D k g) = g := Units.ext (cj_cj g.1)

theorem continuous_cj {m n : ℕ} : Continuous (cj : Mx D m n → Mx D m n) :=
  continuous_id.matrix_map GlobalTheory.FockCompare.ThetaCont.continuous_conj

theorem continuous_cjG (k : ℕ) : Continuous (cjG D k) := by
  refine Units.continuous_iff.2 ⟨continuous_cj.comp Units.continuous_val, ?_⟩
  exact continuous_cj.comp Units.continuous_coe_inv

theorem mem_iff (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F (-V.gram)) ↔ cjG D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  show (g.1ᵀ * incM D.host.F (-V.gram) * g.1.map (cAl D) : Mx D V.rank V.rank) = incM D.host.F (-V.gram) ↔
    (adj (cj g.1) * rat V.gram * cj g.1 : Mx D V.rank V.rank) = rat V.gram
  rw [map_cAl, incM_eq, rat_neg, adj_eq, cj_cj, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def conjEquiv (V : HSp D) : UD D (-V.gram) ≃ₜ* GA D V where
  toFun h := (⟨cjG D V.rank h.1, (mem_iff V h.1).1 h.2⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  invFun g := ⟨cjG D V.rank (matHom V g), (mem_iff V _).2 (by
    rw [cjG_cjG]; exact (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2)⟩
  left_inv h := Subtype.ext (cjG_cjG h.1)
  right_inv g := Subtype.ext (cjG_cjG (matHom V g))
  map_mul' h h' := Subtype.ext (map_mul (cjG D V.rank) h.1 h'.1)
  continuous_toFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _

theorem isConjV_conjEquiv (V : HSp D) : IsConjV V (conjEquiv V) := fun _ => rfl


theorem mem_ratU_iff (V : HSp D) (h : UD D (-V.gram)) : h ∈ ratU D.sp.cm.sig (-V.gram) ↔ conjEquiv V h ∈ GQ V := by
  constructor
  · rintro ⟨γ, hγ⟩
    rw [mem_GQ_iff]
    refine ⟨γ.1.map D.sp.cm.sig, ?_⟩
    have h1 : (rat γ.1 : Mx D V.rank V.rank) = umat h := congrArg Units.val hγ
    show (rat (γ.1.map D.sp.cm.sig) : Mx D V.rank V.rank) = cj (umat h)
    rw [← h1, cj_rat]
  · rintro ⟨γ, -, hγ⟩
    refine ⟨Matrix.GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) γ, Units.ext ?_⟩
    have h1 : (rat γ.1 : Mx D V.rank V.rank) = cj (umat h) := congrArg Units.val hγ
    show (rat (γ.1.map D.sp.cm.sig) : Mx D V.rank V.rank) = umat h
    rw [← cj_rat, h1, cj_cj]

theorem exists_conj : ∀ (D : D7) (V : HSp D), ∃ ι : UD D (-V.gram) ≃ₜ* GA D V, IsConjV V ι ∧ ∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V :=
  fun _ V => ⟨conjEquiv V, isConjV_conjEquiv V, mem_ratU_iff V⟩

end GlobalTheory.SWLink.Conj

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_conj_hermitian_automorphisms : ∀ (D : D7) (V : HSp D), ∃ ι : UD D (-V.gram) ≃ₜ* GA D V, IsConjV V ι ∧ ∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V := by
  atlas_forward_decl GlobalTheory.SWLink.Conj.exists_conj
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Darb

section General

variable {F E A ι : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [FiniteDimensional F E]

theorem trace_one_tmul (z : E) :
    Algebra.trace A (A ⊗[F] E) (1 ⊗ₜ z) = algebraMap F A (Algebra.trace F E z) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext y
  simp

theorem sum_repr_dual [Algebra.IsSeparable F E] [Fintype ι] [DecidableEq ι] (ε : Module.Basis ι F E) (a b : A ⊗[F] E) :
    ∑ k, (Algebra.TensorProduct.basis A ε).repr a k * (Algebra.TensorProduct.basis A ε.traceDual).repr b k =
      Algebra.trace A (A ⊗[F] E) (a * b) := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis A ε).sum_repr a, ← (Algebra.TensorProduct.basis A ε.traceDual).sum_repr b,
    Finset.sum_mul_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, trace_one_tmul, Module.Basis.trace_mul_traceDual, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]

end General

variable {D : D7} {m n d : ℕ}

theorem cj_smul (a : AF D.host.F) (x : Mx D m n) : cj (a • x) = a • cj x := by
  rw [← map_cAl, ← map_cAl]
  funext i j
  exact map_smul (cAl D) a (x i j)

theorem cat_add {R : Type} [Add R] (p y p' y' : Matrix (Fin m) (Fin n) R) :
    cat (p + p') (y + y') = cat p y + cat p' y' := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_smul {S R : Type} [SMul S R] (a : S) (p y : Matrix (Fin m) (Fin n) R) :
    cat (a • p) (a • y) = a • cat p y := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cat_map {S R : Type} (f : R → S) (p y : Matrix (Fin m) (Fin n) R) :
    (cat p y).map f = cat (p.map f) (y.map f) := by
  funext i j
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp [cat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

def ptLin (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) →ₗ[AF D.host.F] Mx D m (n + n) where
  toFun p := pt T p.1 p.2
  map_add' p p' := by
    rw [Prod.fst_add, Prod.snd_add, pt, pt, pt, cj_add, cj_add, cat_add, Matrix.add_mul]
  map_smul' a p := by
    rw [Prod.smul_fst, Prod.smul_snd, pt, pt, cj_smul, cj_smul, cat_smul, Matrix.smul_mul, RingHom.id_apply]

def ptEquiv (T : GL (Fin (n + n)) D.host.E) (m : ℕ) : (Mx D m n × Mx D m n) ≃ₗ[AF D.host.F] Mx D m (n + n) :=
  LinearEquiv.ofBijective (ptLin T m)
    ⟨fun _ _ h => Prod.ext (pt_inj h).1 (pt_inj h).2, fun u => by
      obtain ⟨q, x, h⟩ := exists_pt T u
      exact ⟨(q, x), h.symm⟩⟩

theorem ptEquiv_symm (T : GL (Fin (n + n)) D.host.E) (q x : Mx D m n) : (ptEquiv T m).symm (pt T q x) = (q, x) :=
  (ptEquiv T m).symm_apply_eq.2 rfl

def gramEquiv (V : HSp D) (n : ℕ) : Mx D V.rank n ≃ₗ[AF D.host.F] Mx D V.rank n where
  toFun q := cj (-(gA V ⬝ q))
  map_add' q q' := by rw [Matrix.mul_add, neg_add, cj_add]
  map_smul' a q := by rw [Matrix.mul_smul, ← smul_neg, cj_smul, RingHom.id_apply]
  invFun y := -(giA V ⬝ cj y)
  left_inv q := by
    show -(giA V ⬝ cj (cj (-(gA V ⬝ q))) : Mx D V.rank n) = q
    rw [cj_cj, Matrix.mul_neg, neg_neg, giA_gA_cancel]
  right_inv y := by
    show cj (-(gA V ⬝ (-(giA V ⬝ cj y) : Mx D V.rank n))) = y
    rw [Matrix.mul_neg, neg_neg, gA_giA_cancel, cj_cj]

def coEquiv (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Mx D V.rank (n + n) ≃ₗ[AF D.host.F]
      (Fin V.rank × Fin n × Fin d → AF D.host.F) × (Fin V.rank × Fin n × Fin d → AF D.host.F) :=
  (ptEquiv T V.rank).symm ≪≫ₗ LinearEquiv.prodComm _ _ _ ≪≫ₗ
    (coordL ε V.rank n).prodCongr (gramEquiv V n ≪≫ₗ coordL ε.traceDual V.rank n)

theorem coEquiv_pt (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (q x : Mx D V.rank n) : coEquiv V T ε (pt T q x) = (coord ε x, coord ε.traceDual (cj (-(gA V ⬝ q)))) := by
  rw [coEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, ptEquiv_symm]
  rfl

theorem coord_dot (ε : Module.Basis (Fin d) D.host.F D.host.E) (x y : Mx D m n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj y) = StdUnn.trA (Matrix.trace (adj x ⬝ y : Mx D n n)) := by
  have h : Matrix.trace (adj x ⬝ y : Mx D n n) = ∑ i, ∑ j, cA D (x i j) * y i j := by
    rw [Finset.sum_comm]; rfl
  rw [h, StdUnn.trA, map_sum, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (sum_repr_dual ε (x i j) (cA D (y i j))).trans ?_
  refine Eq.trans ?_ (trA_cA _)
  rw [map_mul (cA D), cA_cA]

theorem coord_dot_gram (V : HSp D) (ε : Module.Basis (Fin d) D.host.F D.host.E) (x q : Mx D V.rank n) :
    coord ε x ⬝ᵥ coord ε.traceDual (cj (-(gA V ⬝ q))) = -StdUnn.trA (Matrix.trace (StdUnn.inner V x q)) := by
  rw [coord_dot, Matrix.mul_neg, Matrix.trace_neg, StdUnn.trA, map_neg]
  rfl

theorem coord_rat (ε : Module.Basis (Fin d) D.host.F D.host.E) (γ : Matrix (Fin m) (Fin n) D.host.E) :
    coord ε (rat γ : Mx D m n) = fun p => algebraMap D.host.F (AF D.host.F) (ε.repr (γ p.1 p.2.1) p.2.2) := by
  funext p
  show (Algebra.TensorProduct.basis (AF D.host.F) ε).repr (1 ⊗ₜ γ p.1 p.2.1) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem exists_pt_rat (T : GL (Fin (n + n)) D.host.E) (u : Matrix (Fin m) (Fin (n + n)) D.host.E) :
    ∃ q x : Matrix (Fin m) (Fin n) D.host.E, (rat u : Mx D m (n + n)) = pt T (rat q) (rat x) := by
  obtain ⟨p, y, h⟩ := exists_cat (u * (T⁻¹).1ᵀ)
  refine ⟨p.map D.sp.cm.sig, y.map D.sp.cm.sig, ?_⟩
  have h1 : u = cat p y * T.1ᵀ := by
    rw [← h, Matrix.mul_assoc, ← Matrix.transpose_mul, T.mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [pt, ← cj_rat, ← cj_rat, cj_cj, cj_cj, h1, rat_mul, rat, cat_map]
  rfl

theorem coEquiv_form (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (w w' : Mx D V.rank (n + n)) :
    symp (R := AF D.host.F) (cAl D) (-1) (incM D.host.F (-V.gram)) (incM D.host.F J₂) w w' =
      (coEquiv V T ε w).1 ⬝ᵥ (coEquiv V T ε w').2 - (coEquiv V T ε w').1 ⬝ᵥ (coEquiv V T ε w).2 := by
  obtain ⟨q, x, rfl⟩ := exists_pt T w
  obtain ⟨q', x', rfl⟩ := exists_pt T w'
  rw [symp_pt V hG, coEquiv_pt, coEquiv_pt]
  dsimp only
  rw [coord_dot_gram, coord_dot_gram, trA_inner_comm V q x', neg_sub_neg]

def co (V : HSp D) {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E}
    (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Dbx V J₂ d := ⟨coEquiv V T ε, coEquiv_form V hG ε⟩

theorem coEquiv_rat (V : HSp D) (T : GL (Fin (n + n)) D.host.E) (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (u : Matrix (Fin V.rank) (Fin (n + n)) D.host.E) : ∃ y z : Fin V.rank × Fin n × Fin d → D.host.F,
    coEquiv V T ε (rat u) =
      (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  obtain ⟨q, x, h⟩ := exists_pt_rat T u
  have h1 : coEquiv V T ε (rat u) =
      (coord ε (rat x), coord ε.traceDual (rat ((-(V.gram * q)).map D.sp.cm.sig))) := by
    rw [h, coEquiv_pt, gA, ← rat_mul, ← rat_neg, cj_rat]
  rw [coord_rat, coord_rat] at h1
  exact ⟨_, _, h1⟩

theorem exists_adapted (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E)
    (hT : IsWittBasis D.sp.cm.sig J 1 T) (hG : T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n)
    (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  refine ⟨co V hG ε, ⟨coEquiv_rat V T ε, fun u hu => ?_, fun u hu => ?_⟩, fun q x => ?_⟩
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_diag_iff hT q x).1 hu
    exact (congrArg Prod.fst (coEquiv_pt V T ε q 0)).trans (coord_zero ε)
  · obtain ⟨q, x, rfl⟩ := exists_pt T u
    obtain rfl := (pt_anti_iff hT q x).1 hu
    refine (congrArg Prod.snd (coEquiv_pt V T ε 0 x)).trans ?_
    rw [Matrix.mul_zero, neg_zero, cj_zero]
    exact coord_zero _
  · refine ⟨congrArg Prod.fst (coEquiv_pt V T ε q x), fun x' => ?_⟩
    exact (congrArg (fun p => coord ε x' ⬝ᵥ Prod.snd p) (coEquiv_pt V T ε q x)).trans (coord_dot_gram V ε x' q)

end GlobalTheory.SWLink.Darb

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_basis_adapted_coordinates : ∀ (D : D7) (n : ℕ) (V : HSp D) (J : Matrix (Fin n) (Fin n) D.host.E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), IsWittBasis D.sp.cm.sig J 1 T → T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ co : Dbx V J₂ d, IsAdapted D.sp.cm.sig co ∧ IsCoord V T ε co := by
  atlas_forward_decl GlobalTheory.SWLink.Darb.exists_adapted
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkMeas

theorem map_covol {G H : Type} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [AddGroup H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalAddGroup H] (e : G ≃+ H) (h1 : Continuous e) (h2 : Continuous e.symm) (Γ : AddSubgroup G)
    (Λ : AddSubgroup H) (hΓ : ∀ x, x ∈ Γ ↔ e x ∈ Λ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hv : μ 𝓕 = 1) :
    ∃ μ' : Measure H, (μ'.IsAddHaarMeasure ∧ ∃ 𝓕' : Set H, μ' 𝓕' = 1 ∧ IsAddFundamentalDomain Λ 𝓕' μ') ∧
      ∀ f : H → ℂ, ∫ y, f y ∂μ' = ∫ x, f (e x) ∂μ := by
  let t : G ≃ₜ H := { e.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  let E : G ≃ᵐ H := t.toMeasurableEquiv
  have hE : (E : G → H) = e := rfl
  refine ⟨μ.map e, ⟨AddEquiv.isAddHaarMeasure_map μ e h1 h2, e '' 𝓕, ?_, ?_⟩, fun f => integral_map_equiv E f⟩
  · rw [← hE, E.map_apply, Set.preimage_image_eq _ E.injective, hv]
  · let q : Λ ≃ Γ :=
      { toFun := fun y => ⟨e.symm y, (hΓ _).2 (by simpa using y.2)⟩
        invFun := fun x => ⟨e x, (hΓ _).1 x.2⟩
        left_inv := fun y => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun x => Subtype.ext (e.symm_apply_apply _) }
    have hp : MeasurePreserving E μ (μ.map e) := ⟨E.measurable, rfl⟩
    refine h𝓕.image_of_equiv E.toEquiv (hp.symm E).quasiMeasurePreserving q fun g x => ?_
    show e (e.symm g + x) = g + e x
    rw [map_add, e.apply_symm_apply]

variable {D : D7} {m n d : ℕ}

theorem continuous_coord (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (coord ε : Mx D m n → _) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact continuous_pi fun p =>
    ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))

theorem continuous_coordL_symm (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (coordL ε m n).symm := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  exact continuous_pi fun i => continuous_pi fun j =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply (i, j, k))

theorem coord_rat (ε : Module.Basis (Fin d) D.host.F D.host.E) (γ : Matrix (Fin m) (Fin n) D.host.E)
    (p : Fin m × Fin n × Fin d) :
    coord ε (rat γ : Mx D m n) p = algebraMap D.host.F (AF D.host.F) (ε.repr (γ p.1 p.2.1) p.2.2) := by
  show (Algebra.TensorProduct.basis (AF D.host.F) ε).repr ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ p.1 p.2.1) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem mem_ratMx_iff (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    x ∈ ratMx D m n ↔ coord ε x ∈
      (AddMonoidHom.compLeft (algebraMap D.host.F (AF D.host.F)).toAddMonoidHom (Fin m × Fin n × Fin d)).range := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨fun p => ε.repr (γ p.1 p.2.1) p.2.2, funext fun p => (coord_rat ε γ p).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨Matrix.of fun i j => ε.equivFun.symm fun k => c (i, j, k), (coord_bijective ε).1 ?_⟩
    rw [← hc]
    funext p
    refine (coord_rat ε _ p).trans ?_
    exact congrArg (algebraMap D.host.F (AF D.host.F))
      (congrFun (ε.equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2)

theorem exists_isTamagawa : ∀ (D : D7) (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), IsCovolOne (ratMx D m n) μ 𝓕 → ∀ [MeasurableSpace (Fin m × Fin n × Fin d → AF D.host.F)] [BorelSpace (Fin m × Fin n × Fin d → AF D.host.F)], ∃ μ' : Measure (Fin m × Fin n × Fin d → AF D.host.F), IsTamagawa D.host.F (Fin m × Fin n × Fin d) μ' ∧ ∀ f : (Fin m × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ := by
  intro D m n d ε μ 𝓕 h _ _
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact map_covol (coordL ε m n).toAddEquiv (continuous_coord ε) (continuous_coordL_symm ε) (ratMx D m n) _
    (mem_ratMx_iff ε) μ 𝓕 h.1 h.2.1 h.2.2

end GlobalTheory.SWLinkMeas

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tamagawa_measure_matrix_adeles : ∀ (D : D7) (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), IsCovolOne (ratMx D m n) μ 𝓕 → ∀ [MeasurableSpace (Fin m × Fin n × Fin d → AF D.host.F)] [BorelSpace (Fin m × Fin n × Fin d → AF D.host.F)], ∃ μ' : Measure (Fin m × Fin n × Fin d → AF D.host.F), IsTamagawa D.host.F (Fin m × Fin n × Fin d) μ' ∧ ∀ f : (Fin m × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ := by
  atlas_forward_decl GlobalTheory.SWLinkMeas.exists_isTamagawa
end

section
section
noncomputable section

namespace GlobalTheory.SWTrans

theorem exists_extend {G X : Type} [Monoid G] [AddCommGroup X] [Module ℂ X] (S : Submodule ℂ X)
    (ρ : G →* Module.End ℂ S) : ∃ om : G →* Module.End ℂ X, ∀ g (Φ : S), om g Φ.1 = (ρ g Φ).1 := by
  obtain ⟨C, hC⟩ := S.exists_isCompl
  let e := S.prodEquivOfIsCompl C hC
  let P : G →* Module.End ℂ (S × C) :=
    { toFun := fun g => LinearMap.prodMap (ρ g) LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g h => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toRingHom.toMonoidHom).comp P, fun g Φ => ?_⟩
  change e (P g (e.symm Φ.1)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]

theorem exists_trans {G H X Y : Type} [Monoid G] [Monoid H] (S : Submodule ℂ (X → ℂ)) (e : X ≃ Y) (a : H → X → X)
    (h1 : ∀ x, a 1 x = x) (hm : ∀ h h' x, a (h * h') x = a h' (a h x))
    (hS : ∀ h, ∀ Φ ∈ S, (fun x => Φ (a h x)) ∈ S) (ω : G →* Module.End ℂ S)
    (hc : ∀ h g (Φ Ψ : S), (∀ x, Ψ.1 x = Φ.1 (a h x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (a h x)) :
    ∃ om : H × G →* Module.End ℂ (Y → ℂ), ∀ h g (φ : Y → ℂ) (Φ : S), φ ∘ e = Φ.1 →
      ∀ x, om (h, g) φ (e x) = (ω g Φ).1 (a h x) := by
  let L : H →* Module.End ℂ S :=
    { toFun := fun h => (LinearMap.funLeft ℂ ℂ (a h)).restrict (hS h)
      map_one' := by
        ext Φ x
        exact congrArg Φ.1 (h1 x)
      map_mul' := fun h h' => by
        ext Φ x
        exact congrArg Φ.1 (hm h h' x) }
  have hL : ∀ h g, Commute (L h) (ω g) := fun h g => by
    ext Φ x
    exact (hc h g Φ (L h Φ) (fun _ => rfl) x).symm
  obtain ⟨om, hom⟩ := exists_extend S (L.noncommCoprod ω hL)
  let c : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.symm
  refine ⟨(c.conjRingEquiv.toRingHom.toMonoidHom).comp om, fun h g φ Φ hφ x => ?_⟩
  change om (h, g) (φ ∘ e) (e.symm (e x)) = _
  rw [hφ, hom, e.symm_apply_apply]
  rfl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

theorem exists_isTrans : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  intro D n V ψ χ θ hθ μ 𝓕 hμ ω hω J₂ d ε ι κ
  have key := GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω
  obtain ⟨om, hom⟩ := exists_trans (H := UD D (-V.gram)) (schwartzA θ V.rank n) (coordL ε V.rank n).toEquiv
    (fun h x => (mt V (ι h)⁻¹ ⬝ x : Mx D V.rank n))
    (fun x => by simp only [map_one, inv_one, GlobalTheory.MixModel.mt_one, Matrix.one_mul])
    (fun h h' x => by simp only [map_mul, mul_inv_rev, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc])
    (fun h => (key (ι h)⁻¹).1) (ω.comp κ.toMonoidHom) (fun h g => (key (ι h)⁻¹).2 (κ g))
  refine ⟨om, ?_, fun h g φ _ Φ hφ x => hom h g φ Φ hφ x⟩
  rintro ⟨h, g⟩ φ hφ
  have h1 := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  obtain ⟨φ', h2⟩ := GlobalTheory.SchwartzCoord.exists_schA_comp_coord_eq D θ hθ V.rank n d ε _
    ((key (ι h)⁻¹).1 _ (ω (κ g) ⟨_, h1⟩).2)
  have h3 : om (h, g) φ = φ'.1 := by
    funext y
    obtain ⟨x, rfl⟩ := (coord_bijective (m := V.rank) (n := n) ε).2 y
    exact (hom h g φ ⟨_, h1⟩ rfl x).trans (congrFun h2 x).symm
  rw [h3]
  exact φ'.2

end GlobalTheory.SWTrans

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_seesaw_schwartz : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  atlas_forward_decl GlobalTheory.SWTrans.exists_isTrans
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink

theorem exists_transport_mean {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup G) (Δ : Subgroup H) [DiscreteTopology Δ] (ι : G ≃ₜ* H)
    (hι : ∀ h, h ∈ Γ ↔ ι h ∈ Δ) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ (ν' : Measure G) (𝓕 : Set G), ν'.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 ν' ∧
      ∀ f : H → ℂ, LeftInv Δ f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend Δ f q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Δ ν := by
  have h₀ := isFundamentalDomain_stdDom Δ ν
  let e : G ≃ᵐ H := ι.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (ν.map e.symm) ν := ⟨e.measurable, e.map_map_symm⟩
  refine ⟨ν.map e.symm, e ⁻¹' stdDom Δ, ι.symm.isHaarMeasure_map ν, ?_, fun f hf => ?_⟩
  · refine h₀.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ : Δ => (⟨ι.symm δ, (hι _).2 (by rw [ι.apply_symm_apply]; exact δ.2)⟩ : Γ))
      ⟨fun a b hab => ?_, fun γ => ?_⟩ fun δ x => ?_
    · exact Subtype.ext (ι.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ι γ, (hι _).1 γ.2⟩, Subtype.ext (ι.symm_apply_apply _)⟩
    · exact (map_mul ι (ι.symm δ) x).trans (congrArg (· * ι x) (ι.apply_symm_apply _))
  · rw [setAverage_eq, average_eq, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h₀, measureReal_def, measureReal_def,
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h₀,
      hp.measure_preimage_equiv]
    simp only [hf.descend_mk]
    exact congrArg _ (hp.setIntegral_preimage_emb e.measurableEmbedding f _)

theorem exists_fundDom_mean : ∀ (D : D7) (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V), (∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V) → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ (ν' : Measure (UD D (-V.gram))) (𝓕 : Set (UD D (-V.gram))), ν'.IsHaarMeasure ∧ IsFundamentalDomain (ratU D.sp.cm.sig (-V.gram)) 𝓕 ν' ∧ ∀ f : GA D V → ℂ, LeftInv (GQ V) f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, descend (GQ V) f q ∂autMeasure V ν := by
  intro D V ι hι ν hν
  have : BorelSpace (UD D (-V.gram)) := ⟨rfl⟩
  exact exists_transport_mean _ _ ι hι ν

end GlobalTheory.SWLink
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_average_fundamental_domain_descent : ∀ (D : D7) (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V), (∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V) → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ (ν' : Measure (UD D (-V.gram))) (𝓕 : Set (UD D (-V.gram))), ν'.IsHaarMeasure ∧ IsFundamentalDomain (ratU D.sp.cm.sig (-V.gram)) 𝓕 ν' ∧ ∀ f : GA D V → ℂ, LeftInv (GQ V) f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, descend (GQ V) f q ∂autMeasure V ν := by
  atlas_forward_decl GlobalTheory.SWLink.exists_fundDom_mean
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}
  {J : Matrix (Fin n) (Fin n) D.host.E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
  {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n} {ι : UD D (-V.gram) ≃ₜ* GA D V} {d : ℕ}
  {ε : Module.Basis (Fin d) D.host.F D.host.E} {co : Dbx V J₂ d}
  {om : UD D (-V.gram) × UD D J₂ →* Module.End ℂ ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ)}

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem isHermND_neg_gram (V : HSp D) : IsHermND D.sp.cm.sig ((1 : D.host.E) • -V.gram) := by
  rw [one_smul]
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.neg_apply, Matrix.neg_apply, map_neg]
    exact congrArg Neg.neg (congrFun (congrFun (gram_conjTranspose V) i) j)
  · rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_isUnit_det V).ne_zero

theorem aniso_neg_gram (hV : IsAniso V) (x : Fin V.rank → D.host.E)
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (-V.gram) x x = 0) : x = 0 := by
  by_contra h0
  refine hV 1 (Matrix.of fun i _ => star (x i)) ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => h0 (funext fun i => ?_)
    exact star_eq_zero.1 (congrFun h i)
  · funext a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero] at hx
    rw [cT_sig, Matrix.mul_assoc, Matrix.zero_apply, ← hx]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star, dotProduct, Matrix.mulVec]
    rfl

theorem height {K : Subgroup (UD D J₂)} {H : StdUnn.G D n → ℝ≥0} (hH : StdUnn.IsHeight H)
    (hP : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ StdUnn.P D n)
    (ha : ∀ p : siegelOf finSumFinEquiv (uinc D J₂),
      StdUnn.blkA (StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1)
    (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n) :
    IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K ∧ ∀ g, hgtOf finSumFinEquiv (uinc D J₂) (absA D) K g = H (κ g) := by
  have h1 : ∀ (p : siegelOf finSumFinEquiv (uinc D J₂)), ∀ k ∈ K,
      H (κ (p * k)) = absA D (aOf finSumFinEquiv (uinc D J₂) p) := fun p k hk => by
    rw [map_mul]
    exact hH _ ((hP p).1 p.2) _ (ha p) _ ((hK k).1 hk)
  have h2 : IwasawaOf finSumFinEquiv (uinc D J₂) (absA D) K := by
    refine ⟨fun g => ?_, fun p hp => ?_⟩
    · obtain ⟨p, hp, k, hk, e⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (κ g)
      refine ⟨⟨κ.symm p, (hP _).2 (by rwa [κ.apply_symm_apply])⟩, κ.symm k, (hK _).2 (by rwa [κ.apply_symm_apply]), ?_⟩
      rw [← map_mul, ← e, κ.symm_apply_apply]
    · have e1 := h1 p 1 (one_mem K)
      have e2 := h1 1 p hp
      rw [mul_one] at e1
      rw [OneMemClass.coe_one, one_mul, map_one, map_one] at e2
      exact e1.symm.trans e2
  refine ⟨h2, fun g => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := h2.1 g
  rw [h2.hgtOf_mul p hk, h1 p k hk]

theorem kfin (hom : IsTrans ε ι κ ω om) {K : Subgroup (UD D J₂)} (hK : ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ StdUnn.K D n)
    {φ : (Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ}
    (hφ : φ ∈ schA D.host.F (Fin V.rank × Fin n × Fin d)) (Φ : schwartzA θ V.rank n) (e : φ ∘ coord ε = Φ.1)
    (hΦ : RegSch.KFin ω Φ) : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) φ}) := by
  let L : schwartzA θ V.rank n →ₗ[ℂ] ((Fin V.rank × Fin n × Fin d → AF D.host.F) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (coordL ε V.rank n).symm).comp (schwartzA θ V.rank n).subtype
  haveI : FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}) := hΦ
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ
    {Ψ : schwartzA θ V.rank n | ∃ k ∈ StdUnn.K D n, Ψ = ω k Φ}).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨ω (κ k) Φ, Submodule.subset_span ⟨κ k, (hK k).1 hk, rfl⟩, funext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (coordL ε V.rank n).surjective y
  rw [coordL_apply, hom.right k hφ Φ e]
  exact congrArg (ω (κ k) Φ).1 ((coordL ε V.rank n).symm_apply_apply x)

theorem skew_xi (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  refine ⟨D.host.xi0, GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, D.host.φ₀.injective ?_⟩
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [(GlobalTheory.AdelicU.isCMExt_host D).2.2.2, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

end GlobalTheory.SWLink

end
end
