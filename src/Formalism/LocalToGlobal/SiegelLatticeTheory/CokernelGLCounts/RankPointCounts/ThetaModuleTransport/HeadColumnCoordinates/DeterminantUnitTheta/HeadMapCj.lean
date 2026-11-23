module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Asm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem ind_det (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R} (γ : IsoMbe Z₁.Z Z₂.Z)
    (θ θ' : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (h : Ind hs γ θ) (h' : Ind hs γ θ') : θ = θ' := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H l =>
    obtain ⟨l₂, hl₂⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk l))
    exact (h l l₂ hl₂.symm).trans (h' l l₂ hl₂.symm).symm

theorem map_cj_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map M.L.cj = Zh := by
  ext a b; simp [M.L.cj_cj]

theorem det_map_cj {n : Type} [Fintype n] [DecidableEq n] (Zh : Matrix n n E) :
    (Zh.map M.L.cj).det = M.L.cj Zh.det := by
  have := RingHom.map_det (M.L.cj : E →+* E) Zh
  simpa [RingHom.mapMatrix_apply] using this.symm

theorem head_map_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ((Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [← det_map_cj]
  rfl

theorem gHyp_cj {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ : M.Mat (r + 1)}
    (h : GHyp M g T T' TT Zh Z Zσ) : GHyp M g T T' TT (Zh.map M.L.cj) Zσ Z := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h5, by rw [map_cj_cj]; exact h4, by rw [det_map_cj]; exact h6.map _, ?_⟩
  rw [det_map_cj, head_map_cj, M.L.cj_cj, M.L.cj_cj, mul_comm (M.L.cj Zh.det),
    mul_comm (M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)]
  exact h7

theorem kapEq_cj {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : KapEq Zh₁ Zh₂) :
    KapEq (Zh₁.map M.L.cj) (Zh₂.map M.L.cj) := by
  unfold KapEq at h ⊢
  rw [det_map_cj, det_map_cj, head_map_cj, head_map_cj, ← map_mul, ← map_mul, h]

end Asm

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
