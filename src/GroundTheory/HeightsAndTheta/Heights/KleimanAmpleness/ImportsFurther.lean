module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelChangeNef.proof (hC : ModelCurves.Statement) (hN : ModelCurveNum.Statement) :
    ModelChangeNef.Statement := by
  have key : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
      IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
      ∀ (β : K → ℤ) (β' : K' → ℤ),
        (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
            secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
        IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β → IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β' := by
    intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs hnef W' hW' hle' hrel'
    obtain ⟨hP, hPle, hPrel⟩ := (hC F K' ι' Ω y' k₀' N e' _ hx hm' 1).1 W' hW' hle' hrel'
    obtain ⟨W, hW, hle, hrel, hWP⟩ := (hC F K ι Ω y k₀ N e _ rfl hm 1).2 _ hP hPle hPrel
    rw [← hN F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hWP]
    exact hnef W hW hle hrel
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs
  exact ⟨key F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs,
    key F Ω N K' ι' y' k₀' e' K ι y k₀ e hm' hm hx.symm β' β fun c => (hs c).symm⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
