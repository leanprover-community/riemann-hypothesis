module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem

namespace GlobalTheory.Mem.Col2

theorem fOk_of_fieldsOk {X : Fields} (hX : X.Ok) (σ : X.K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) :
    FOk X.emb σ :=
  ⟨hX.conjE, hX.emb_star, hσ⟩

theorem base_fOk (B : Base) : letI := B.fields.starE; FOk B.fields.emb B.embLL :=
  fOk_of_fieldsOk (GlobalTheory.Mem.FieldsLaws.fields_ok B) B.embLL B.starLL_cx

theorem base_fields_primes_ok : ∀ (B : Base) (X : PreX B.toPre),
    B.fields.Ok ∧ (B.primes X).Ok ∧ B.wts.Ok ∧ (letI := B.host.cmStar; FOk B.tauLL B.embLL) ∧
      2 * B.fields.f * B.R.k < (B.primes X).g 0 - 1 := fun B X =>
  ⟨GlobalTheory.Mem.FieldsLaws.fields_ok B, (GlobalTheory.BasePrimes.primes_ok B X).1,
    { row_ok τ := ⟨B.hc τ, rfl⟩
      hc_row u τ := by
        show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
        unfold RowPar.of
        rw [B.hcW_v, B.hcW_b, B.hcW_e]
      u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
      u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm },
    base_fOk B, by rw [B.fields_f]; exact X.g_big 0⟩

end GlobalTheory.Mem.Col2
