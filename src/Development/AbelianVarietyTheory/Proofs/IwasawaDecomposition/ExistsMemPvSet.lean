module

public import Formalism.LocalToGlobal.UnitaryNorms.DefsDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.Statement
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.QLocTied

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

end GlobalTheory.PlaceOverPair
