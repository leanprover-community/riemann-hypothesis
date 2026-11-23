module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelD
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegelC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem siegelSmall_of_k (hF : SliceFacts) (hAC : AdaptedChar) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar
  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]
  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]
  obtain ⟨t', ht', hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring
end PositivityTheory.SiegelWeilFormula.Ald
end
end
