module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
public import Mathlib
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DetIdealsKernelNormOne
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Reduction
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantOfTrianglesData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.OneEntryMem
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PullMulRight
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNormOne
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemStandardThetaLatticeIffAdelicIdeal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.FinrankRow
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuConc
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ReductionOf
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFacts
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLComm
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.RightMoveTrianglesOfUnit
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Family
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfArith
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndepOfGen
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HermitianPairingIntegral
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopIso
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IopNorm
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFourSq
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ThIndep

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.KS

open Formalism.L2.Ker.KS hiding La_le La_stable aaX emV emV_smulE emV_smulO embC_injective embH_iff embV_eq flatV_vecE frame_std gen_eq imS imS_stable inMul_std lamTie mat mat_mem_hom mat_mulVec mat_unmat opM opM_smul phi phi_eq phi_mem_La phi_per phi_smulE phi_smulO thF_eq unitM unitM_mulVec unmat unmat_mem_hom

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Ker.Cd
open Formalism.L2.AlgTh (lamF flat vecE)
open Formalism.L2.Th1.GD (InMul)

variable {D : Car} {X : Fields} (s : Seam D X)

section Maps

variable {a b : ℕ}

def mat (x : HomE X.E a b) : Matrix (Fin b) (Fin a) D.host.E := fun i j => s.iE (x (Pi.single j 1) i)

def unmat (A : Matrix (Fin b) (Fin a) D.host.E) : HomE X.E a b := Matrix.toLin' (A.map s.iE.symm)

theorem mat_unmat (A : Matrix (Fin b) (Fin a) D.host.E) : mat s (unmat s A) = A := by
  funext i j
  simp [mat, unmat, Matrix.toLin'_apply]

theorem mat_mulVec (x : HomE X.E a b) (y : Sp X.E a) : (mat s x).mulVec (s.vec y) = s.vec (x y) := by
  funext i
  have h : x y = ∑ j, y j • x (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  show ∑ j, s.iE (x (Pi.single j 1) i) * s.iE (y j) = s.iE (x y i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

def phi (δ : ℂ) : HomE X.E a b →+ Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun x := fun τ i j => δ * Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def opM (e : D.host.E) : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b →+ Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun v := fun τ i j => Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ e * v τ i j
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def emV : Matrix (Fin b) (Fin a) D.host.E →+ Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun A := fun τ i j => Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (A i j)
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp

theorem embV_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin b) (Fin a) D.host.E) :
    Formalism.L2.Ker.Cd.TaylorLogMetric.embV D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) A = emV A := rfl

theorem opM_smul (e : D.host.E) (w : ℂ) (v : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) : opM e (w • v) = w • opM e v := by
  funext τ i j
  show Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ e * (w * v τ i j) = w * (Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ e * v τ i j)
  ring

theorem emV_smulO (r : 𝓞 D.host.E) (A : Matrix (Fin b) (Fin a) D.host.E) : emV (r • A) = opM (r : D.host.E) (emV A) := by
  funext τ i j
  show Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (r • A i j) = _
  rw [Algebra.smul_def, map_mul]
  rfl

theorem phi_smulO (δ : ℂ) (r : 𝓞 X.E) (x : HomE X.E a b) : phi s δ (r • x) = opM (s.iE (r : X.E)) (phi s δ x) := by
  funext τ i j
  show δ * Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s.iE (r • x (Pi.single j 1) i)) = Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s.iE (r : X.E)) * (δ * _)
  rw [Algebra.smul_def, map_mul, map_mul]
  show δ * (Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s.iE (r : X.E)) * _) = _
  ring

end Maps

section Per

variable {a b : ℕ} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

def aaX : Submodule (𝓞 X.E) X.E :=
  Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}

theorem La_stable (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (r : 𝓞 D.host.E) {v : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b} (hv : v ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L L') :
    opM (r : D.host.E) v ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨w, hw, r • A, Submodule.smul_mem _ _ hA, ?_⟩
    rw [embV_eq, embV_eq, opM_smul, emV_smulO]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg]; exact neg_mem h

theorem mat_mem_hom {x : HomE X.E a b} (hx : x ∈ homO N N') : mat s x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.homL D (s.lat N) (s.lat N') := by
  refine Submodule.subset_span ?_
  intro y hy
  obtain ⟨y₀, hy₀, rfl⟩ := (s.mem_lat N y).1 hy
  rw [mat_mulVec]
  exact (s.mem_lat N' _).2 ⟨x y₀, hx y₀ hy₀, rfl⟩

theorem unmat_mem_hom {A : Matrix (Fin b) (Fin a) D.host.E} (hA : ∀ x ∈ s.lat N, A.mulVec x ∈ s.lat N') : unmat s A ∈ homO N N' := by
  intro y hy
  have h1 := hA (s.vec y) ((s.mem_lat N _).2 ⟨y, hy, rfl⟩)
  rw [← mat_unmat s A, mat_mulVec] at h1
  obtain ⟨z, hz, hzz⟩ := (s.mem_lat N' _).1 h1
  have : z = unmat s A y := by
    funext i
    exact s.iE.injective (congrFun hzz i)
  rw [← this]
  exact hz

theorem gen_eq (c : 𝓞 D.host.K) (t : D.host.E) (x : HomE X.E a b) :
    phi s δ (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • x) =
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • mat s x) := by
  funext τ i j
  show δ * Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (s.iE (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) * x (Pi.single j 1) i)) =
    (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (t * s.iE (x (Pi.single j 1) i))
  rw [map_mul, RingEquiv.apply_symm_apply, map_mul, map_mul, map_mul]
  have h := embOnK D τ (c : D.host.K)
  have h' : Formalism.L2.Ker.Cd.TaylorLogMetric.embT D τ (((c : D.host.K) : D.host.E)) = D.host.φ₀ (((c : D.host.K) : D.host.E)) := h
  rw [h']
  ring

theorem phi_mem_La {z : HomE X.E a b} (hz : z ∈ perO (aaX s cc) N N') :
    phi s δ z ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  have key : ∀ r ∈ aaX s cc, ∀ x ∈ homO N N', phi s δ (r • x) ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r h =>
      obtain ⟨c, hc, t, ht, rfl⟩ := h
      intro x hx
      rw [gen_eq]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, t • mat s x,
        Submodule.subset_span ⟨t, ht, mat s x, mat_mem_hom s N N' hx, rfl⟩, rfl⟩
    | zero => intro x _; rw [zero_smul, map_zero]; exact zero_mem _
    | add r r' _ _ h1 h2 => intro x hx; rw [add_smul, map_add (f := _)]; exact add_mem (h1 x hx) (h2 x hx)
    | smul ρ r _ h =>
      intro x hx
      obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
      rw [smul_assoc, phi_smulO, ← hρ']
      exact La_stable cc δ _ _ ρ' (h x hx)
  induction hz using Submodule.span_induction with
  | mem z h =>
    obtain ⟨r, hr, x, hx, rfl⟩ := h
    exact key r hr x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
  | smul ρ z _ h =>
    obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
    rw [phi_smulO, ← hρ']
    exact La_stable cc δ _ _ ρ' h

def imS : AddSubgroup (Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) := (perO (aaX s cc) N N').toAddSubgroup.map (phi s δ)

theorem imS_stable (r : 𝓞 D.host.E) {v : Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b} (hv : v ∈ imS s cc δ N N') : opM (r : D.host.E) v ∈ imS s cc δ N N' := by
  obtain ⟨z, hz, rfl⟩ := hv
  obtain ⟨ρ, hρ⟩ := (s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
  refine ⟨ρ • z, Submodule.smul_mem _ _ hz, ?_⟩
  rw [phi_smulO]
  have : s.iE ((ρ : 𝓞 X.E) : X.E) = (r : D.host.E) := by
    have h2 : ((ρ : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := hρ
    rw [h2, RingEquiv.apply_symm_apply]
  rw [this]

theorem La_le : Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ≤ imS s cc δ N N' := by
  have key4 : ∀ c ∈ cc, ∀ t ∈ D.host.AA0, ∀ A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.homL D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • A) ∈ imS s cc δ N N' := by
    intro c hc t ht A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      refine ⟨s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • unmat s A,
        Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, t, ht, rfl⟩, unmat s A, unmat_mem_hom s N N' h, rfl⟩, ?_⟩
      rw [gen_eq, mat_unmat]
    | zero => rw [smul_zero, map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [smul_add, map_add (f := _), smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [smul_comm, emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key3 : ∀ c ∈ cc, ∀ A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.YYl D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV A ∈ imS s cc δ N N' := by
    intro c hc A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      obtain ⟨t, ht, A₀, hA₀, rfl⟩ := h
      exact key4 c hc t ht A₀ hA₀
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [map_add (f := _), smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key2 : ∀ w ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ, ∀ A ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.YYl D (s.lat N) (s.lat N'), w • emV A ∈ imS s cc δ N N' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w h =>
      obtain ⟨c, hc, rfl⟩ := h
      exact key3 c hc
    | zero => intro A _; rw [zero_smul]; exact zero_mem _
    | add x y _ _ h1 h2 => intro A hA; rw [add_smul]; exact add_mem (h1 A hA) (h2 A hA)
    | neg x _ h => intro A hA; rw [neg_smul]; exact neg_mem (h A hA)
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.La
  rw [AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, hA, rfl⟩
  exact key2 w hw A hA

theorem phi_per : imS s cc δ N N' = Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact phi_mem_La s cc δ N N' hz
  · exact La_le s cc δ N N'

end Per

section Frame

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

end Frame

end Formalism.L2.Ker.Cd.KS
