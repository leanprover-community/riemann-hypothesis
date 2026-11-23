module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symLevel_character_by_residueCharacter : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue | exact GlobalTheory.symLevel_lam_residue | (intros; apply GlobalTheory.symLevel_lam_residue <;> assumption)
