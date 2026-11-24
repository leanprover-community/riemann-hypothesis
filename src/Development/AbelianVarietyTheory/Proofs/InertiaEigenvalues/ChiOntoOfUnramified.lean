module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramCyc


open PowerSeries in
theorem _root_.GlobalTheory.UnramCyc.chi_onto_of_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (K : _root_.Formalism.BasicNotions.Loc.FinExt l),
    K.1 ≤ _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l → ∀ c : ℤ_[l]ˣ, ∃ g ∈ _root_.Formalism.BasicNotions.Loc.GK K, (P.χQ g : ℚ_[l]) = ((c : ℤ_[l]) : ℚ_[l]) := by
  intro l _ P K hK c
  have hnorm : ‖((c : ℤ_[l]) : ℚ_[l])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units c
  obtain ⟨g, hg, hgc⟩ := _root_.GlobalTheory.Cyc.exists_chi_eq K P.χQ P.χQ_cyc _ hnorm
  have hK0 : _root_.Formalism.BasicNotions.Loc.K0 K = K.1 := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact inf_eq_left.mpr hK
  refine ⟨g, ?_, hgc⟩
  unfold _root_.Formalism.BasicNotions.Loc.GK
  rw [← hK0]
  exact hg

end GlobalTheory.UnramCyc
