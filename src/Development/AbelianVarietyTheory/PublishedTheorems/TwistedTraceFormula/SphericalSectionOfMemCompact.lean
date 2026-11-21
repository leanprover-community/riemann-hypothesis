import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.Model

section Field

variable (E : Type) [Field E] [CharZero E] [StarRing E]

theorem four_gram (e e' : Matrix (Fin 4) (Fin 1) E) (i : Matrix (Fin 4) (Fin 2) E) (he : e = !![0; 0; 1; 1])
    (he' : e' = !![0; 0; 1 / 2; -(1 / 2)]) (hi : i = !![1, 0; 0, 1; 0, 0; 0, 0]) :
    eᴴ * sgnM E ![false, true, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, true, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, true, false, true] * e = 1 ∧ iᴴ * sgnM E ![false, true, false, true] * i = sgnM E ![false, true] ∧
    iᴴ * sgnM E ![false, true, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, true, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b <;> rw [Matrix.mul_apply] <;>
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_four, Examples₂.sgn] <;> norm_num

theorem two_gram (e e' : Matrix (Fin 2) (Fin 1) E) (he : e = !![1; 1]) (he' : e' = !![1 / 2; -(1 / 2)]) :
    eᴴ * sgnM E ![false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, true] * e = 1 := by
  subst he he'
  refine ⟨col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_⟩ <;> simp [Fin.sum_univ_two, Examples₂.sgn]
  norm_num

end Field

def hypFour (D : D7) : HypDec (diagSp D 4 ![false, true, false, true] 2 2) (diagSp D 2 ![false, true] 1 1) 1 where
  e := (!![0; 0; 1; 1] : Matrix (Fin 4) (Fin 1) D.host.E)
  e' := (!![0; 0; 1 / 2; -(1 / 2)] : Matrix (Fin 4) (Fin 1) D.host.E)
  i₀ := (!![1, 0; 0, 1; 0, 0; 0, 0] : Matrix (Fin 4) (Fin 2) D.host.E)
  ee := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 2 _ 1 1).symm
  i₀e := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

def hypTwo (D : D7) : HypDec (diagSp D 2 ![false, true] 1 1) (diagSp D 0 ![] 0 0) 1 where
  e := (!![1; 1] : Matrix (Fin 2) (Fin 1) D.host.E)
  e' := (!![1 / 2; -(1 / 2)] : Matrix (Fin 2) (Fin 1) D.host.E)
  i₀ := 0
  ee := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).1
  e'e' := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).2.1
  e'e := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).2.2
  iso := by funext i; exact i.elim0
  i₀e := by funext i; exact i.elim0
  i₀e' := by funext i; exact i.elim0
  rank_add := rfl



theorem exists_isMaj {D : D7} (V : HSp D) : ∃ a, IsMaj V a :=
  let ⟨a, _, h⟩ := @AdelicU.Frames.exists_isLatticeFrame_isMajorantFrame _ _ _ _ _ _ _ _ _ (AdelicU.isCMExt_host D) _ (isHermND_gram V) _
    (isLattice_frameLat_host V)
  ⟨a, h⟩

theorem exists_haar_Kmax {D : D7} (T : HSp D) (b : GL (Fin T.rank) (AE D)) :
    ∃ ν : Measure (Kmax T b), ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  haveI : CompactSpace (Kmax T b) :=
    isCompact_iff_compactSpace.1 (isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _)
  exact ⟨Measure.haarMeasure ⊤, inferInstance, ⟨Measure.haarMeasure_self⟩⟩


example (D : D7) : rhoH (diagSp D 2 ![false, true] 1 1) 1 = 1 / 2 := by
  show ((2 : ℕ) - (1 : ℕ) : ℝ) / 2 = 1 / 2
  norm_num

theorem sphericalSection_of_mem_compact {D : D7} {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)}
    (h : HasIw d (Kmax T b)) (s : ℂ) {k : GA D T} (hk : k ∈ Kmax T b) : sphericalSection d b s k = 1 := by
  rw [sphericalSection, h.isIwasawa.iwAbs_of_mem hk]; simp [npow]


theorem IsRegElt.unique {D : D7} {S T T₀ : HSp D} {r : ℕ} {ψ : AddChar (AF D.host.F) ℂ}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau} {d : HypDec T T₀ r}
    {b : GL (Fin T.rank) (AE D)} (hI : HasIw d (Kmax T b)) {zG zG' zH : MvPolynomial ℕ ℂ} {P P' : Polynomial ℂ}
    (h : IsRegElt ψ om θ τ d b zG zH P) (h' : IsRegElt ψ om θ τ d b zG' zH P') : P = P' :=
  Polynomial.funext fun s => by
    have := congrFun ((h.2.2.1 s).symm.trans (h'.2.2.1 s)) 1
    simpa only [Pi.smul_apply, sphericalSection_of_mem_compact hI s (one_mem _), smul_eq_mul, mul_one] using this

end GlobalTheory.RegSW.Model

end
