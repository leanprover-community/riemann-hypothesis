import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordFamilySymbolHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCovarianceHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactZeroHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightChartHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightGeneratorWordEvaluation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftGeneratorWordEvaluation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantShiftCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymbolOperatorFieldHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfChartEqs

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nilpotent_of_char_poly : NilOfCharpoly := by
  intro n M h
  have hmon := Matrix.charpoly_monic M
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hX : M.charpoly = (X : ℂ[X]) ^ n := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [if_neg (by omega)]
      have := h (n - i) (by omega) (by omega)
      rwa [show n - (n - i) = i by omega] at this
    · rw [if_pos hi]
      have h1 := hmon.coeff_natDegree
      rw [hdeg] at h1
      rw [hi]; exact h1
    · rw [if_neg (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨n, ?_⟩
  have := Matrix.aeval_self_charpoly M
  rwa [hX, map_pow, Polynomial.aeval_X] at this

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_facts {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 ∧ Hpk k r * g = (g⁻¹)ᴴ * Hpk k r ∧ gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  obtain ⟨-, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg0 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg0, hHH]
  have hr : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp hl
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have hgi : g⁻¹ * g = 1 := by rw [hinv]; exact hl
  have hig : g * g⁻¹ = 1 := by rw [hinv]; exact hr
  refine ⟨hgi, hig, ?_, ?_⟩
  · calc Hpk k r * g = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * g := by
          rw [← Matrix.conjTranspose_mul, hig, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hg0]
  · calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hig, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg0]

theorem conjugation_algebraic_holds : ConjAlg := by
  intro k r g hg
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  refine ⟨fun A hA => ?_, fun A hA => ?_, fun A h0 => ?_, fun A X => ?_⟩
  · unfold B.inLie at hA ⊢
    have e1 : (g * A * g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (Aᴴ * Hpk k r) * g⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [hgH]
    have e2 : Hpk k r * (g * A * g⁻¹) = (g⁻¹)ᴴ * (Hpk k r * A) * g⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [hHg]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hA, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    have hp : ∀ m : ℕ, (g * A * g⁻¹) ^ m = g * A ^ m * g⁻¹ := by
      intro m
      induction m with
      | zero => simp [hig]
      | succ m ih =>
        rw [pow_succ, ih, pow_succ]
        calc g * A ^ m * g⁻¹ * (g * A * g⁻¹) = g * A ^ m * (g⁻¹ * g) * A * g⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = g * (A ^ m * A) * g⁻¹ := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hp, hn, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    apply h0
    calc A = (g⁻¹ * g) * A * (g⁻¹ * g) := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
      _ = g⁻¹ * (g * A * g⁻¹) * g := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · have e : (g * A * g⁻¹) * (g * X * g⁻¹) = g * (A * X * g⁻¹) := by
      calc (g * A * g⁻¹) * (g * X * g⁻¹) = g * A * (g⁻¹ * g) * X * g⁻¹ := by simp only [Matrix.mul_assoc]
        _ = g * (A * X * g⁻¹) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem left_covariance_chart_holds : CovL := by
  intro k r d O U κ Φ hC x hx ξ Ξ₀ _hΞ₀ hcov X hX
  have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  have hY : B.inLie k r ((κ x)⁻¹ * X * κ x) := by
    unfold B.inLie at hX ⊢

    have e1 : ((κ x)⁻¹ * X * κ x)ᴴ * Hpk k r = (κ x)ᴴ * (Xᴴ * Hpk k r) * κ x := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← hHg]
    have e2 : Hpk k r * ((κ x)⁻¹ * X * κ x) = (κ x)ᴴ * (Hpk k r * X) * κ x := by
      simp only [← Matrix.mul_assoc]
      rw [← hgH]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]
  have hV : VL κ Φ X x = VR κ Φ ((κ x)⁻¹ * X * κ x) x := by
    show fderiv ℝ Φ (κ x) (X * κ x) = fderiv ℝ Φ (κ x) (κ x * ((κ x)⁻¹ * X * κ x))
    rw [show κ x * ((κ x)⁻¹ * X * κ x) = X * κ x by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hig, Matrix.one_mul]]
  have ht : Matrix.trace (Ξ₀ * ((κ x)⁻¹ * X * κ x)) = Matrix.trace (κ x * Ξ₀ * (κ x)⁻¹ * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hV, hcov _ hY, ht]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem frame_existence : FrameEx := fun _ _ _ hz hT => Qx8.frame_exists hz hT

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem derivative_local_representative : RdVRep := by
  intro k r E _ _ X U F f hX hU hc he h hh hhG
  have hc' : ContDiffOn ℝ (((1 : ℕ∞) : WithTop ℕ∞)) F U := by exact_mod_cast hc
  refine ⟨LieDecompositionLocal.rdV_eq_fderiv (m := 1) le_rfl hU hh hhG hc' he hX, ?_⟩
  have hd : DifferentiableAt ℝ F h :=
    (hc.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hh)
  have hloc : Q.LdV X f h = Q.LdV X F h := by
    show deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * h)) 0 =
      deriv (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * h)) 0
    apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * h) := by
      have h1 := (gpMulR h).continuous.comp (B5.curve_contDiff (1 : B.Mat k r) X).continuous
      refine h1.congr fun t => ?_
      simp [gpMulR_apply]
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * h ∈ U := by
      apply hcont.continuousAt.preimage_mem_nhds
      have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * h = h := by simp
      rw [h0]
      exact hU.mem_nhds hh
    filter_upwards [hev] with t ht
    exact he _ ht (WeylGroupFacts.uh_mul (B5.exp_mem hX t) hhG)
  rw [hloc]
  exact gp_ldV X h F hd

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cvag_posL_iff {k r : ℕ} (a b : Fin (Q.mdim k r 0)) : Q.posL k r 0 a = Q.posL k r 0 b ↔ a = b := by
  simp [Q.posL, Fin.ext_iff]

theorem cvag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ)
    (σ : Equiv.Perm (Fin (Q.mdim k r 0))) :
    (List.ofFn fun i : Fin (Q.mdim k r 0) =>
      Top (Q.EH (E := E) k r) (u - ((i : ℕ) : ℂ)) (Q.posL k r 0 (σ i)) (Q.posL k r 0 i)) =
      (capGens (zgCV k r) σ).map (fun gn => genOpR (E := E) gn u) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, Formalism.QuantumDeterminants.Top, genOpR, capGen, zgCV, Q.EH, EabH, cvag_posL_iff, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  split_ifs <;> simp

theorem capelli_vector_as_generators : CVAsGens := by
  intro k r E _ _ Y f g
  simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cvag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem crag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpR (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpR, capGen, zgB, Q.RZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem right_capelli_as_generators : CapRAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capR, Q.qmF, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [crag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem clag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpL (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpL, capGen, zgB, Q.LZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem left_capelli_as_generators : CapLAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capLft, Q.qmFrev, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_reverse, List.foldr_reverse, clag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem exponential_degree_holds : FExpDeg := by
  intro k r gens
  induction gens with
  | nil =>
    intro _ t ht
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | cons gn gs ih =>
    intro hdeg t ht
    have hgn : gn.1.natDegree ≤ 1 := hdeg gn (by simp)
    have ih' := ih (fun g hg => hdeg g (List.mem_cons_of_mem _ hg))
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨t', ht', rfl⟩ | ⟨dX, hdX, t', ht', rfl⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_mul_le (p := gn.1) (q := t'.1)
        simp only [List.length_cons]
        omega
      · intro X hX
        obtain ⟨g, hg, d, hd⟩ := h2 X hX
        exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩
    · obtain ⟨h1, h2⟩ := ih' t' ht'
      refine ⟨?_, ?_⟩
      · have := Polynomial.natDegree_C_mul_le dX.1 t'.1
        simp only [List.length_cons]
        omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨gn, by simp, dX.1, hdX⟩
        · obtain ⟨g, hg, d, hd⟩ := h2 X hX
          exact ⟨g, List.mem_cons_of_mem _ hg, d, hd⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

namespace ExponentialSymbolLetters

variable {k r : ℕ} (τ : B.Mat k r → ℂ) (u s : ℂ)

def phi (t : Polynomial ℂ × List (B.Mat k r)) : ℂ := t.1.eval u * s ^ t.2.length * (t.2.map τ).prod

theorem head (p : Polynomial ℂ) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (p * t.1, t.2)).map (phi τ u s)).sum = p.eval u * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul]
  ring

theorem letter (d : ℂ) (X : B.Mat k r) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (Polynomial.C d * t.1, X :: t.2)).map (phi τ u s)).sum =
      (d * s * τ X) * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul, Polynomial.eval_C, List.length_cons, pow_succ,
    List.map_cons, List.prod_cons]
  ring

theorem letters (L : List (ℂ × B.Mat k r)) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((L.flatMap fun dX => l.map fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)).map (phi τ u s)).sum =
      s * (L.map fun dX => dX.1 * τ dX.2).sum * (l.map (phi τ u s)).sum := by
  induction L with
  | nil => simp
  | cons dX L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, letter, ih, List.map_cons, List.sum_cons]
    ring

theorem all (gs : List (GenW k r)) : ((fexp gs).map (phi τ u s)).sum =
    (gs.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod := by
  induction gs with
  | nil => simp [fexp, phi]
  | cons gn gs ih =>
    rw [fexp, List.map_append, List.sum_append, head, letters, List.map_cons, List.prod_cons, ← ih]
    ring

end ExponentialSymbolLetters

theorem exponential_symbol_holds : FExpSymb := by
  intro k r gens τ u s
  exact ExponentialSymbolLetters.all τ u s gens

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem coefficient_interpolation_holds : CoeffInterp := by
  intro N m _hm
  refine ⟨fun i => ((i : ℕ) : ℝ),
    fun i => (Lagrange.basis (Finset.univ : Finset (Fin (N + 1))) (fun j => ((j : ℕ) : ℂ)) i).coeff m, ?_⟩
  intro q hq
  have hinj : Set.InjOn (fun j : Fin (N + 1) => ((j : ℕ) : ℂ)) ((Finset.univ : Finset (Fin (N + 1))) : Set (Fin (N + 1))) := by
    intro a _ b _ hab
    simp only at hab
    exact Fin.ext (by exact_mod_cast hab)
  have hdeg : q.degree < ((Finset.univ : Finset (Fin (N + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hq) (by exact_mod_cast Nat.lt_succ_self N)
  have h := Lagrange.eq_interpolate hinj hdeg
  conv_rhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul]
  simp only [Complex.ofReal_natCast]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem symbol_operator_linear_holds : SOpLin := by
  intro d S T c O hST hS hT
  obtain ⟨o, a⟩ := S
  obtain ⟨o', b⟩ := T
  simp only at hST
  subst hST
  refine ⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    exact (contDiffOn_const.mul (hS i w)).add (hT i w)
  · intro u x
    simp only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro x ξ
    simp only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace IdentityZeroOperators

variable {d : ℕ}

def idOp (d : ℕ) : SOp d := ⟨0, fun _ _ _ => 1⟩

def zeroOp (d m : ℕ) : SOp d := ⟨m, fun _ _ _ => 0⟩

lemma idOp_app (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (idOp d).app u x = u x := by
  change ∑ k : Fin 1, ∑ w : Fin k → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  rw [Fin.sum_univ_one]
  change ∑ w : Fin 0 → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  simp [pdc]

lemma idOp_symb (x ξ : Fin d → ℝ) : (idOp d).symb x ξ = 1 := by
  change ∑ w : Fin 0 → Fin d, (∏ i : Fin 0, (ξ (w i) : ℂ)) * (1 : ℂ) = 1
  simp

lemma zeroOp_app (m : ℕ) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (zeroOp d m).app u x = 0 := by
  simp [SOp.app, zeroOp]

lemma zeroOp_symb (m : ℕ) (x ξ : Fin d → ℝ) : (zeroOp d m).symb x ξ = 0 := by
  simp [SOp.symb, zeroOp]

lemma word (hF : SOpField) (O : Set (Fin d → ℝ)) (hO : IsOpen O) :
    ∀ Vs : List ((Fin d → ℝ) → (Fin d → ℝ)), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = Vs.length ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O → ∀ x ∈ O,
        S.app u x = vfW Vs u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = (Vs.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod
  | [], _ => ⟨idOp d, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [idOp_app, vfW],
      fun x _ ξ => by simp [idOp_symb]⟩
  | V :: Vs, hV => by
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := word hF O hO Vs (fun W hW => hV W (List.mem_cons_of_mem _ hW))
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hF d S V O hO hSc (hV V List.mem_cons_self)
    refine ⟨S', by rw [hS'o, hSo]; rfl, hS'c, ?_, ?_⟩
    · intro u hu x hx
      have hl : (V :: Vs).length = S.ord + 1 := by rw [hSo]; rfl
      rw [hl] at hu
      have hu0 : ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O :=
        hu.of_le (by rw [hSo]; exact_mod_cast Nat.le_succ _)
      rw [hS'a u hu x hx]
      have he : S.app u =ᶠ[nhds x] vfW Vs u := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact hSa u hu0 y hy
      simp only [vfW, vfD]
      rw [he.fderiv_eq]
    · intro x hx ξ
      rw [hS's x hx ξ, hSs x hx ξ]
      simp

end IdentityZeroOperators

open IdentityZeroOperators in
theorem vector_to_symbol_operator : VOpToSOpOfSteps := by
  intro hF hL hLin d m P O hO hP
  induction P with
  | nil =>
    exact ⟨zeroOp d m, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [zeroOp_app, WOp.app],
      fun x _ ξ => by simp [zeroOp_symb, WOp.symb]⟩
  | cons t P ih =>
    obtain ⟨T, hTo, hTc, hTa, hTs⟩ := ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))
    obtain ⟨hlen, hsm⟩ := hP t List.mem_cons_self
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := word hF O hO t.2 hsm
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hL d S m O (by rw [hSo]; exact hlen) hSc
    obtain ⟨R, hRo, hRc, hRa, hRs⟩ := hLin d S' T t.1 O (hS'o.trans hTo.symm) hS'c hTc
    refine ⟨R, hRo.trans hS'o, hRc, ?_, ?_⟩
    · intro u hu x hx
      rw [hRa, hS'a, hSa u (hu.of_le (by exact_mod_cast hlen)) x hx, hTa u hu x hx]
      simp [WOp.app]
    · intro x hx ξ
      rw [hRs, hS's, hSs x hx ξ, hTs x hx ξ, hSo]
      simp only [WOp.symb, List.map_cons, List.sum_cons]
      split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem chartEqs_of_capJoints (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) :
    ChartEqs := by
  obtain ⟨h4, h5, h6⟩ := capWords_all_of hJ hJR hJL derivative_local_representative right_exponential_evaluation left_exponential_evaluation capelli_vector_as_generators
    right_capelli_as_generators left_capelli_as_generators exponential_degree_holds exponential_symbol_holds determinant_shift_coefficient coefficient_interpolation_holds
  exact chartEqs_of_J operator_capelli_vector operator_right_capelli operator_left_capelli nilpotent_of_char_poly conjugation_algebraic_holds left_covariance_chart_holds
    chart_covariance_holds right_chart_holds nilpotent_lie_finite_holds h4 h5 h6 compact_zero_holds frame_existence vector_to_symbol_operator
    symbol_operator_field_holds symbol_operator_lift_holds symbol_operator_linear_holds

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
