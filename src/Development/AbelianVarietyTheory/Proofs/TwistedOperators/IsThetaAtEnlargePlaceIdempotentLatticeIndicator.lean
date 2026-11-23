module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaEnlarge

theorem isThetaAt_enlarge : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ {f₀ : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) f₀ →
    ∀ {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P →
    ∀ {Φ g : WO S T → ℂ}, IsSBHalf e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ Φ g →
    IsSBHalf e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) g := by
  intro D S T ψ θ sS sT ΛS ΛT hS hT f₀ hvac e e' P P' he he' hsub Φ g hΦ hg
  obtain ⟨b, rfl, hb, hab⟩ := GlobalTheory.RowLocVec.exists_compl_idem hsub he he'
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  rw [add_sub_cancel_left]
  exact GlobalTheory.RowLocVec.isThetaAt_extend hvac.1 hS hT he ha hb hab hvac.2.lat hΦ hg

end GlobalTheory.ThetaEnlarge

end
