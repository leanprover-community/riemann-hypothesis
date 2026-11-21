import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj

section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVec_mem_theta_space : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → ∀ o : ℕ, cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
  first | exact @GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT | exact GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT | (intros; apply GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT <;> assumption)
end

section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.RepSum

theorem congOne_one {D : D7} {a : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} : CongOne D 𝔪 (1 : GA D a) := by
  intro i j
  simp

end GlobalTheory.FunObj.SqNum.RepSum

namespace GlobalTheory.FunObj.SqNum

end GlobalTheory.FunObj.SqNum
end
end

section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

theorem conj_smul_conj_smul {D : D7} (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => GlobalTheory.NormSum.VacMove.conj_conj D x
  rw [smul_smul, h, one_smul]

end GlobalTheory.FunObj.NormUniq
end

section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

theorem cosetVec_mem_TT {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) :
    cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d :=
  GlobalTheory.T.cosetVec_mem_theta_space P h𝔪 o

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m)

end GlobalTheory.FunObj.NormUniq

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

end GlobalTheory.FunObj.NormUniq

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m)

end GlobalTheory.FunObj.NormUniq
end
end
