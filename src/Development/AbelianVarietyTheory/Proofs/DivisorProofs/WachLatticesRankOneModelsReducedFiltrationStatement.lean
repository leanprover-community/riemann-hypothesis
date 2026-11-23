module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration
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

open NumberField GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  first | exact @GlobalTheory.WachPlace.wach_lattices | exact GlobalTheory.WachPlace.wach_lattices | (intros; apply GlobalTheory.WachPlace.wach_lattices <;> assumption)
