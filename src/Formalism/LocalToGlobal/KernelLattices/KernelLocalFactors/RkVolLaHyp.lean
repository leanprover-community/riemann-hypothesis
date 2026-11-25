module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Mathlib.RingTheory.PiTensorProduct
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam, Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain, Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat, Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp

-- ===== clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam =====
-- clump-header: {"m": "Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth\npublic import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective\n\n"}
section -- clump:auto
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

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  show ∑ j, s.iE (x (Pi.single j 1) i) * s.iE (y j) = s.iE (x y i)

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

def unitM {a b : ℕ} (e : D.host.E) (β : Fin b) (α : Fin a) : Matrix (Fin b) (Fin a) D.host.E :=
  fun i j => if i = β ∧ j = α then e else 0

end Frame

end Formalism.L2.Ker.Cd.KS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam =====

-- ===== clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain =====
-- clump-header: {"m": "Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd\npublic import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.Cd.KS

open Formalism.L2.Ker.KS hiding La_left La_nsmul La_right YYl_nsmul al_flat alpha_flat fixed_pb fnPow_eq form_flat homL_nsmul inter_pb lamM' latPow_eq locNorm_ambOf_of locNorm_thF_of opU_pb pb relIdx_pb reps_pb selfDual_pb semi_pb thF_ambOf thM' th_pb

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (Sesq IsHerm IsPosDef altE opU dualLat IsSelfDual IsSemiChar fixedBy sumU IsReps relIdx inter Th IsLat matH alphaQ
  CmOK cosetRepsExist InterReps_of semicharacterHom)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (hSc hPow latPow fnPow LocNormScale LocNormPow LocNormInter)

section Gen

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)

abbrev pb (Λ : AddSubgroup W) : AddSubgroup V := Λ.comap e.toLinearMap.toAddMonoidHom

theorem relIdx_pb (Λ₁ Λ₂ : AddSubgroup W) : relIdx (pb e Λ₁) (pb e Λ₂) = relIdx Λ₁ Λ₂ := by
  unfold relIdx
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  exact e.surjective

variable (H : Sesq V) (H' : Sesq W) (hH : ∀ x y, H x y = H' (e x) (e y))

include hH

alias opU_pb := _root_.Formalism.L2.Ker.KS.opU_pb

theorem semi_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x))
    (h : IsSemiChar H' Λ α') : IsSemiChar H (pb e Λ) α := by
  refine ⟨fun x hx => by rw [hα x hx]; exact h.1 _ hx, fun x hx y hy => ?_⟩
  have hx' : e x ∈ Λ := hx
  have hy' : e y ∈ Λ := hy
  have hxy : e (x + y) ∈ Λ := by rw [map_add (f := _)]; exact Λ.add_mem hx' hy'
  rw [hα _ hxy, hα x hx', hα y hy', map_add (f := _), h.2 _ hx' _ hy']
  simp only [altE, hH]

theorem fixed_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x)) {F : W → ℂ}
    (h : F ∈ fixedBy H' α' Λ) : (fun v => F (e v)) ∈ fixedBy H α (pb e Λ) := by
  intro x hx z
  have hx' : e x ∈ Λ := hx
  rw [opU_pb e H H' hH, hα x hx']
  exact h _ hx' _

theorem selfDual_pb {Λ : AddSubgroup W} (h : IsSelfDual H' Λ) : IsSelfDual H (pb e Λ) := by
  unfold IsSelfDual at h ⊢
  ext x
  constructor
  · intro hx
    show e x ∈ Λ
    rw [← h]
    intro y' hy'
    obtain ⟨m, hm⟩ := hx (e.symm y') (show e (e.symm y') ∈ Λ by simpa using hy')
    refine ⟨m, ?_⟩
    simpa [altE, hH] using hm
  · intro hx
    have hx' : e x ∈ dualLat H' Λ := by
      rw [h]
      exact hx
    intro y hy
    obtain ⟨m, hm⟩ := hx' (e y) hy
    refine ⟨m, ?_⟩
    simpa [altE, hH] using hm

theorem reps_pb {Λ₁ Λ₂ : AddSubgroup W} {S : Finset W} (hS : IsReps Λ₁ Λ₂ S) :
    IsReps (pb e Λ₁) (pb e Λ₂) (S.map e.symm.toEquiv.toEmbedding) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    show e (e.symm y) ∈ Λ₂
    rw [e.apply_symm_apply]
    exact hS.1 y hy
  · intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    have : e (e.symm x' - e.symm y') ∈ Λ₁ := hxy
    rw [map_sub, e.apply_symm_apply, e.apply_symm_apply] at this
    rw [hS.2.1 x' hx' y' hy' this]
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hS.2.2 (e y) hy
    refine ⟨e.symm x, Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    show e (y - e.symm x) ∈ Λ₁
    rwa [map_sub, e.apply_symm_apply]

theorem inter_pb (hH' : IsHerm H') (Λ₁ Λ₂ : AddSubgroup W) (α : V → ℂ) (α' : W → ℂ)
    (hα₁ : ∀ x, e x ∈ Λ₁ → α x = α' (e x)) (hα₂ : ∀ x, e x ∈ Λ₂ → α x = α' (e x))
    (hS : IsSemiChar H' Λ₂ α') (hidx : relIdx Λ₁ Λ₂ ≠ 0) (F : W → ℂ) (hF : F ∈ fixedBy H' α' Λ₁) :
    inter H α (pb e Λ₁) (pb e Λ₂) (fun v => F (e v)) = fun z => inter H' α' Λ₁ Λ₂ F (e z) := by
  funext z
  obtain ⟨⟨S, hSr⟩, -⟩ := cosetRepsExist W Λ₁ Λ₂ hidx
  rw [InterReps_of semicharacterHom W H' hH' Λ₁ Λ₂ α' hS F hF S hSr (e z),
    InterReps_of semicharacterHom V H (herm_pb e H H' hH hH') _ _ α (semi_pb e H H' hH hα₂ hS) _
      (fixed_pb e H H' hH hα₁ hF) _ (reps_pb e H H' hH hSr) z, relIdx_pb]
  congr 1
  simp only [sumU, Finset.sum_map]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : e (e.symm x) ∈ Λ₂ := by rw [e.apply_symm_apply]; exact hSr.1 x hx
  show α (e.symm x) * opU H (e.symm x) (fun v => F (e v)) z = _
  rw [opU_pb e H H' hH, hα₂ _ hx2, e.apply_symm_apply]

end Gen

section GenTh

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  (e : V ≃ₗ[ℂ] W) (H : Sesq V) (H' : Sesq W) (hH : ∀ x y, H x y = H' (e x) (e y))

include hH in
theorem th_pb {Λ : AddSubgroup W} {α : V → ℂ} {α' : W → ℂ} (hα : ∀ x, e x ∈ Λ → α x = α' (e x)) {F : W → ℂ}
    (h : F ∈ Th H' α' Λ) : (fun v => F (e v)) ∈ Th H α (pb e Λ) := by
  refine ⟨?_, fixed_pb e H H' hH hα h.2⟩
  have h1 : AnalyticOnNhd ℂ (LinearMap.toContinuousLinearMap e.toLinearMap) Set.univ :=
    (LinearMap.toContinuousLinearMap e.toLinearMap).analyticOnNhd _
  exact h.1.comp h1 (fun _ _ => Set.mem_univ _)

end GenTh

section Flat

variable {D : Car} {X : Fields} (s : Seam D X) {a b : ℕ}

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def lamM' : AddSubgroup (X.Tau → ℂ) :=
  B.lamM.comap (LinearEquiv.funCongrLeft ℂ ℂ s.iT.symm).toLinearMap.toAddMonoidHom

def thM' : (X.Tau → ℂ) → ℂ := fun z => B.thMM fun τ => z (s.iT.symm τ)

end Flat

end Formalism.L2.Ker.Cd.KS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain =====

-- ===== clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat =====
-- clump-header: {"m": "Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolKerStd\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta\npublic import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP\nimport Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.Cd.KS.Lat

open Formalism.L2.Ker.KS.Lat hiding La_theta al_eq_La alphaQ_isom delta_ne eNat_laF form_flat herm_hSc img_comap isLat_La isLat_comap isLat_laF isom_flat matH_hSc odd_of_cmOK posDef_hSc relIdx_comap relIdx_laF relIdx_laF_eq sc_pos selfDual_comap selfDual_laF thHalf_laF thMoved_laF thZero_laF th_comap th_laF theta_laF

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (hSc)
open Formalism.L2.Th1.F (cmTheta)

section Gen

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] {H : Sesq V} {H' : Sesq W} (g : V ≃ₗ[ℂ] W)

theorem img_comap (Λ' : AddSubgroup W) :
    imgLat (g : V →ₗ[ℂ] W) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = Λ' :=
  AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ'

theorem selfDual_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} (h : IsSelfDual H' Λ') :
    IsSelfDual H (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  unfold IsSelfDual at h ⊢
  ext x
  constructor
  · intro hx
    show g x ∈ Λ'
    rw [← h]
    intro y hy
    obtain ⟨m, hm⟩ := hx (g.symm y) (by show g (g.symm y) ∈ Λ'; rw [g.apply_symm_apply]; exact hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    have h1 := hI x (g.symm y)
    have h2 : (g : V →ₗ[ℂ] W) (g.symm y) = y := g.apply_symm_apply y
    rw [h2] at h1
    unfold altE
    rw [← h1]
    rfl
  · intro hx y hy
    have hx' : g x ∈ dualLat H' Λ' := by rw [h]; exact hx
    obtain ⟨m, hm⟩ := hx' (g y) hy
    refine ⟨m, ?_⟩
    rw [← hm]
    unfold altE
    rw [← hI x y]
    rfl

theorem isLat_comap {Λ' : AddSubgroup W} (h : IsLat Λ') : IsLat (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  constructor
  · have := h.1
    let f : (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) → Λ' := fun x => ⟨g x.1, x.2⟩
    have hf : Continuous f :=
      Continuous.subtype_mk (((g : V →ₗ[ℂ] W).continuous_of_finiteDimensional).comp continuous_subtype_val) _
    have hinj : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (g.injective (congrArg Subtype.val hxy))
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro v _
    let p : W →ₗ[ℝ] V := (g.symm : W →ₗ[ℂ] V).restrictScalars ℝ
    have h2 : (Submodule.span ℝ (Λ' : Set W)).map p ≤
        Submodule.span ℝ ((Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom : AddSubgroup V) : Set V) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      apply Submodule.subset_span
      show g (g.symm y) ∈ Λ'
      rw [g.apply_symm_apply]
      exact hy
    refine h2 ⟨g v, by rw [h.2]; trivial, ?_⟩
    show g.symm (g v) = v
    exact g.symm_apply_apply v

theorem th_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} {α' : W → ℂ} {G : W → ℂ} (hG : G ∈ Th H' α' Λ') :
    (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  refine (ThIsom_of heisenbergIsometry V W H H' g hI _ α' G).1 ?_
  rw [img_comap]
  exact hG

theorem relIdx_comap (Λ₁ Λ₂ : AddSubgroup W) :
    relIdx (Λ₁.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = relIdx Λ₁ Λ₂ := by
  unfold relIdx
  rw [AddSubgroup.relIndex_comap]
  congr 1
  exact AddSubgroup.map_comap_eq_self_of_surjective (f := (g : V →ₗ[ℂ] W).toAddMonoidHom) g.surjective Λ₂

theorem alphaQ_isom (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) (c : ℝ) (v : V) : alphaQ c H' (g v) = alphaQ c H v := by
  unfold alphaQ Formalism.L2.Th1.H.qOf
  have := hI v v
  rw [← this]
  rfl

end Gen

section Form

variable {D : Car} {X : Fields} (s : Seam D X)

theorem isom_flat (A : ℝ) (a b : ℕ) :
    IsIsom (matH (hSc X.Tau a b A⁻¹)) (formV A D.what₂.Tau a b)
      ((s.flatV a b : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) : (DVar X.Tau a b → ℂ) →ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b) :=
  fun x y => (form_flat s A a b x y).symm

theorem matH_hSc (sc : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b sc) x y = (sc : ℂ) * ∑ k, x k * conj (y k) := by
  show (∑ i, ∑ j, x i * hSc X.Tau a b sc i j * conj (y j)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · unfold hSc
    rw [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hj
    unfold hSc
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem herm_hSc (sc : ℝ) (a b : ℕ) : IsHerm (matH (hSc X.Tau a b sc)) := by
  intro x y

  rw [matH_hSc, matH_hSc, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem posDef_hSc {sc : ℝ} (hsc : 0 < sc) (a b : ℕ) : IsPosDef (matH (hSc X.Tau a b sc)) := by
  intro x hx
  rw [matH_hSc]
  have h1 : (∑ k, x k * conj (x k)) = ((∑ k, Complex.normSq (x k) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => Complex.mul_conj (x k)
  rw [h1, ← Complex.ofReal_mul, Complex.ofReal_re]
  apply mul_pos hsc
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ k, Complex.normSq_pos.2 hk⟩

end Form

section Lat

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

include B in
theorem sc_pos : 0 < (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹ := by
  rw [show TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  exact inv_pos.2 (Formalism.L2.Th1.F.areaPos_thm B.L)

theorem delta_ne (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

variable {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

theorem theta_laF {b₀ : ℤ} (hb : Odd b₀) {x : DVar X.Tau a b → ℂ} (hx : x ∈ s.laF B.tor L L') :
    cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L' := by
  obtain ⟨k, rfl⟩ := hb
  have h1 : cmTheta (2 * k + 1) D.host.d = (k : ℂ) + cmTheta 1 D.host.d := by
    unfold cmTheta
    push_cast
    ring
  show s.flatV a b (cmTheta (2 * k + 1) D.host.d • x) ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L'
  rw [map_smul, h1, add_smul]
  refine add_mem ?_ (La_theta B hx)
  have h2 : ((k : ℂ) • s.flatV a b x) = k • s.flatV a b x := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
  rw [h2]
  exact AddSubgroup.zsmul_mem _ hx k

theorem odd_of_cmOK {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (h : CmOK a₀ b₀ c₀ d) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := h
  by_contra hcon
  rw [Int.not_odd_iff_even] at hcon
  obtain ⟨k, rfl⟩ := hcon
  have h4 : (d : ℤ) % 8 = 7 := by exact_mod_cast h3
  have h5 : 4 * ((a₀ : ℤ) * c₀) = 4 * (k * k) + d := by rw [← mul_assoc, h1]; ring
  generalize (a₀ : ℤ) * c₀ = u at h5
  generalize k * k = v at h5
  omega

theorem al_eq_La (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b L L') :
    ∀ x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor L L', Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor x =
      alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) x := by
  intro x hx
  obtain ⟨m, hm⟩ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b L L' hA x hx
  exact al_eq D B.tor x m hm

end Lat

end Formalism.L2.Ker.Cd.KS.Lat
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat =====

-- ===== clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp =====
-- clump-header: {"m": "Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolSeam\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolChain\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\nimport Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLat\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Per

variable {D : Car} {X : Fields} (s : Seam D X) {a b : ℕ}

def Seam.ptE (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] Formalism.L2.Ker.Cd.TaylorLogMetric.VC D a b where
  toFun t := fun τ => t (s.iT.symm τ)
  invFun z := fun τ => z (s.iT τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv t := by funext τ; simp
  right_inv z := by funext τ; simp

theorem ptE_embH (hok : s.Ok) (δ : ℂ) (x : HomE X.E a b) : s.ptE a b (embH (X.embC s.σ₀) δ x) = Formalism.L2.Ker.Cd.KS.phi s δ x := by
  funext τ i j
  show δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  rw [hok.1, Equiv.apply_symm_apply]

theorem lamC_eq (hok : s.Ok) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N' = Formalism.L2.Ker.Cd.KS.pb (s.ptE a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.La D (Formalism.L2.Ker.Cd.TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')) := by
  ext t
  rw [← Formalism.L2.Ker.Cd.KS.phi_per]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (ptE_embH s hok δ x).symm⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, (s.ptE a b).injective ?_⟩
    rw [ptE_embH s hok]
    exact h

theorem HV_ptE (A : ℝ) (x y : VCx X.Tau a b) : HV A⁻¹ x y = formV A D.what₂.Tau a b (s.ptE a b x) (s.ptE a b y) := by
  simp only [HV, formV, LinearMap.mk₂'ₛₗ_apply]
  rw [div_eq_inv_mul, Complex.ofReal_inv]
  congr 1
  refine Fintype.sum_equiv s.iT _ _ (fun τ => ?_)
  simp [Seam.ptE]

end Per

section Facts

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ}
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem alV_ptE (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) (x : VCx X.Tau a b)
    (hx : s.ptE a b x ∈ Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :
    alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹ x = Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor (s.ptE a b x) := by
  rw [Formalism.L2.Ker.Cd.KS.Lat.al_eq_La B hcc hδ hA _ hx]
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [HV_ptE s]

theorem laFacts_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    LaFacts (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc
      (ambOf s B χ cD : Amb X).AA N N' := by
  have hL := (B.latAll hcc hδ (Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ)).1 a b _ _ hA
  show IsSelfDual (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N') ∧
    IsSemiChar (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N') (alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)
  rw [lamC_eq s hok]
  exact ⟨Formalism.L2.Ker.Cd.KS.selfDual_pb (s.ptE a b) _ _ (HV_ptE s _) hL.1,
    Formalism.L2.Ker.Cd.KS.semi_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) hL.2⟩

theorem e_fixed_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : Formalism.L2.Ker.Cd.TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    (ambOf s B χ cD : Amb X).e a b N N' ∈ fixedBy (HV (ambOf s B χ cD : Amb X).sc) (alV (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc)
      (LamC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).AA N N') := by
  have h1 : B.eNat χ a b (s.lat N) (s.lat N') ∈ Th (formV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (Formalism.L2.Ker.Cd.TaylorLogMetric.al D B.tor)
      (Formalism.L2.Ker.Cd.TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :=
    Submodule.smul_mem _ (Formalism.L2.Ker.Cd.Base.chiFac χ a b (s.lat N) (s.lat N'))
      (B.thMoved_mem (B.latAll hcc hδ (Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)
  show (fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.ptE a b z)) ∈ fixedBy (HV (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹)
    (alV D.host.d (TaylorLogMetric.area (Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (Formalism.L2.Ker.Cd.KS.aaX s cc) N N')
  rw [lamC_eq s hok]
  exact Formalism.L2.Ker.Cd.KS.fixed_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) h1.2

end Facts

section IdealS

variable {D : Car} {X : Fields} (s : Seam D X)

def Seam.oE : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

theorem oE_symm_coe (r : 𝓞 D.host.E) : ((s.oE.symm r : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := rfl

def Seam.PrimeTo (I : Ideal (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := ∃ t ∈ I, s.oE.symm t ∉ P.asIdeal

theorem primeTo_top (P : HeightOneSpectrum (𝓞 X.E)) : s.PrimeTo ⊤ P := ⟨1, Submodule.mem_top, by
  rw [map_one]
  exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩

theorem primeTo_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {P : HeightOneSpectrum (𝓞 X.E)} (hI : s.PrimeTo I P) : s.PrimeTo J P := by
  obtain ⟨t, ht, htP⟩ := hI
  exact ⟨t, h ht, htP⟩

theorem primeTo_half {P : HeightOneSpectrum (𝓞 X.E)} (h : s.PrimeTo (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) P) : s.PrimeTo D.host.𝔟 P := by
  refine primeTo_mono s ?_ h
  rw [D.host.𝔟_spec.1]
  exact Submodule.mul_le.mpr fun x hx y _ => D.host.𝔟.mul_mem_right y hx

theorem half_ne_bot (D : Car) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem exists_integral_mul_order_element {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {t : D.host.E} (ht : t ∈ D.host.AA0) :
    ∃ w : 𝓞 D.host.E, (w : D.host.E) = (t₀ : D.host.E) * t := by
  have hb : (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact half_ne_bot D
  have ht' : t ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := ht
  have hm := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 D.host.E)) h₀) ht'
  rw [mul_inv_cancel₀ hb, FractionalIdeal.mem_one_iff] at hm
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, hw⟩

variable (cc : Ideal (𝓞 D.host.K))

theorem half_smul_aa {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {r : X.E} (hr : r ∈ Formalism.L2.Ker.Cd.KS.aaX s cc) :
    s.oE.symm t₀ • r ∈ (1 : Submodule (𝓞 X.E) X.E) := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, t, ht, rfl⟩ := hx
    obtain ⟨w, hw⟩ := exists_integral_mul_order_element h₀ ht
    rw [Submodule.mem_one]
    refine ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    show ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w) : 𝓞 X.E) : X.E) = ((s.oE.symm t₀ : 𝓞 X.E) : X.E) * _
    rw [oE_symm_coe, oE_symm_coe, ← map_mul]
    congr 1
    rw [show ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E)
        = ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (w : D.host.E)
        from map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _, hw]
    rw [show ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E)
        = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) from rfl]
    ring
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hx

theorem aa_fg : (Formalism.L2.Ker.Cd.KS.aaX s cc).FG := by
  obtain ⟨t₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (half_ne_bot D)
  have hu : ((s.oE.symm t₀ : 𝓞 X.E) : X.E) ≠ 0 := by
    rw [oE_symm_coe, map_ne_zero_iff _ s.iE.symm.injective]
    exact_mod_cast hne
  refine (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _
    (Submodule.fg_span_singleton (((s.oE.symm t₀ : 𝓞 X.E) : X.E)⁻¹)))) _ ?_
  intro r hr
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp (half_smul_aa s cc h₀ hr)
  rw [Submodule.mem_span_singleton]
  refine ⟨y, ?_⟩
  rw [Algebra.smul_def] at hy ⊢
  have e : algebraMap (𝓞 X.E) X.E (s.oE.symm t₀) = ((s.oE.symm t₀ : 𝓞 X.E) : X.E) := rfl
  rw [e] at hy
  rw [hy, mul_comm, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem aa_unit_at (P : HeightOneSpectrum (𝓞 X.E)) (hb : s.PrimeTo D.host.𝔟 P)
    (hc : s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    localization₂ P.asIdeal (Formalism.L2.Ker.Cd.KS.aaX s cc) = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  obtain ⟨t₀, h₀, hβ⟩ := hb
  obtain ⟨c, hcc, hγ⟩ : ∃ c ∈ cc, s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) ∉ P.asIdeal := by
    obtain ⟨t, ht, hnt⟩ := hc
    by_contra H
    push Not at H
    have h1 : cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ P.asIdeal.comap (s.oE.symm : 𝓞 D.host.E →+* 𝓞 X.E) :=
      Ideal.map_le_iff_le_comap.2 fun c hc => H c hc
    exact hnt (h1 ht)
  ext x
  rw [mem_locP, mem_locP]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    refine ⟨s.oE.symm t₀ * σ, fun h => (P.isPrime.mem_or_mem h).elim hβ hσ, ?_⟩
    rw [mul_smul]
    exact half_smul_aa s cc h₀ hx
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
    refine ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) * σ, fun h => (P.isPrime.mem_or_mem h).elim hγ hσ, ?_⟩
    have hmem : ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) ∈ Formalism.L2.Ker.Cd.KS.aaX s cc :=
      Submodule.subset_span ⟨c, hcc, 1, Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.one_mem_inverse_halfDifferent D, by rw [mul_one]; rfl⟩
    have e : s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) • algebraMap (𝓞 X.E) X.E o =
        o • ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm]
    rw [mul_smul, ← ho, e]
    exact Submodule.smul_mem _ o hmem

end IdealS

section NatS

variable {D : Car} {X : Fields} (s : Seam D X)

end NatS

section Main

variable {D : Car} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

include s in
theorem nonempty_tau : Nonempty X.Tau := by
  have h2 : 0 < D.R.f := by
    show 0 < 2 * D.R.ord
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have h3 : 0 < @Fintype.card D.what₂.Tau D.what₂.instTau := by
    rw [D.what₂.card_Tau]
    exact h2
  haveI : Nonempty D.what₂.Tau := (@Fintype.card_pos_iff _ D.what₂.instTau).mp h3
  exact s.iT.nonempty

theorem laHyp_ambOf (hok : s.Ok) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P)
    (hcur : ∀ P ∈ Sall, s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall :=
  ⟨Formalism.L2.Ker.Cd.KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, fun P hP => aa_unit_at s cc P (hhalf P hP) (hcur P hP), aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

theorem laHyp_ambOf_top {δ : ℂ} (B : Base D (⊤ : Ideal (𝓞 D.host.K)) δ) (hok : s.Ok) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D ⊤ δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall := laHyp_ambOf s B χ cD hok ⟨top_ne_bot, by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _⟩ hδ ha hb Sall hconj hhalf
    (fun P _ => by rw [Ideal.map_top]; exact primeTo_top s P)

end Main

section Bad

open Formalism.EigenvalueLevelCeiling (plc)

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

variable {sel}

variable (sel)

end Bad

section Chain

variable {D : Car} {X : Fields} {Pr : Primes X} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Chain

end Formalism.L2.Ker.Cd
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp =====
