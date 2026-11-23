module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem baseEx : BaseEx := by
  intro F E _ _ _ _ _ σ hc emb mα mβ
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F
  obtain ⟨a, -, ha⟩ := GlobalTheory.StdRescale.exists_isStd_mulShift F hc.1 ψ₀ hψ₀
  obtain ⟨v₁, -, ⟨τ₁⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hc ∅
  refine ⟨⟨ψ₀.mulShift (algebraMap F (AF F) a), emb, mα, mβ, ∅,
    fun v => absurd v.2 (Finset.notMem_empty _), v₁, τ₁⟩, rfl, rfl, rfl, rfl, ha, fun hu hg => ?_⟩
  exact
    { cm := hc
      galois := hg.1
      unram := hu
      std := ha
      inert := fun v w h => by
        obtain ⟨h2, h3, hd⟩ := hg.2 v w h
        exact ⟨h2, h3, PositivityTheory.Mix.psiUnr_of_not_le ha v hd⟩
      psiP := fun v hv => absurd hv (Finset.notMem_empty _) }

end UpperTheory.Gal.TP.Skew

end
