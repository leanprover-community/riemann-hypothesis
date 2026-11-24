module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

theorem HA_ext {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g g' : HA R σ J}
    (h : ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) : g = g' :=
  Subtype.ext (Units.ext h)

theorem tupH_alt {E : Type} {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_last]

theorem tupH_e {E : Type} {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]

theorem tupH_f {E : Type} {M r : ℕ} (P : Frame E M r) (b : Fin r) :
    tupH P (Fin.natAdd (r + 1) b) = P.f b := by
  simp [tupH, Fin.append_right]

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_piG]
  have H := datR_hyp (R := R) hσσ hJ hP
  refine Fin.addCases (fun b0 => ?_) (fun b1 => ?_) b
  · refine Fin.lastCases ?_ (fun a => ?_) b0
    · rw [tupH_alt]; exact PG.Dat.unipotent_proj_fixes_normal H _
    · rw [tupH_e]; exact PG.Dat.Pi_e H _ a
  · rw [tupH_f]; exact PG.Dat.Pi_f H _ b1

theorem mat_mul (g g' : HA R σ J) : ((HA.mat R σ J (g * g') : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) * ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) := rfl

theorem piG_mat (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    ((HA.mat R σ J (piG hσσ hJ hP g hg) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = piMat (P := P) (T := T) g := rfl

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    piG hσσ hJ hP (g * g') ((S0 R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  apply HA_ext
  rw [mat_mul hσσ hJ hP, piG_mat, piG_mat, piG_mat, piMat, piMat, piMat, Pi_lin_mul hσσ hJ hP hg hg',
    LinearMap.toMatrix'_comp]

theorem spanR_eq {m : ℕ} (Y : Fin m → Fin M → E) :
    spanR (F := F) R Y Set.univ = Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  rw [spanR, Set.image_univ]

end R

end PI.VolSemiDirect.W
