module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminant

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.SkewMove

variable {D : D7}

open Classical in

set_option maxHeartbeats 1000000 in
theorem exists_skew_move : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ, ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧ x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' := by
  intro D 𝔪 h𝔪 hcop d
  obtain ⟨g', x', h1, h2, h3, h4, -⟩ := GlobalTheory.SkewCentral.exists_central_skew_move D 𝔪 h𝔪 hcop d
  exact ⟨g', x', h1, h2, h3, h4⟩

end GlobalTheory.SkewMove
