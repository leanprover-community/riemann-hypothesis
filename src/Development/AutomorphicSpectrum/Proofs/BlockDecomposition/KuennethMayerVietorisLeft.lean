module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem glue_r : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hM hC K _ E U₁ ι _ _ V W hV hW h₁ h₂ hK
  refine GlobalTheory.T.cosieve_pairing_family_compat hM hC E.F₂ E.F₃ (fun a => CH.cx (U₁.ι ⋙ E.F₁ a))
    (fun U U' => (∀ T, U' T → U₁ (E.L₁.obj T)) ∧ (∀ T, U' T → U (E.L₂.obj T)))
    (fun U U' r {a a' c} ha => E.pr U₁ U U' r.1 r.2 ha) ?_ V W hV hW (fun S => ⟨h₁ S, h₂ S⟩)
    (fun S hS => hK S hS)
  intro A B A' B' r₁ r₂ k k' a a' c ha i j n hn x y
  have h := GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 (le_refl U₁) k k' ha hn x y
  rw [GlobalTheory.T.restrict_self_pullC_eq] at h
  exact h

end GlobalTheory.CompanionTheory.KunGlue
