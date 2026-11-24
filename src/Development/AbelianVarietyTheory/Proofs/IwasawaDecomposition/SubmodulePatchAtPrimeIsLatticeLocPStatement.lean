module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

theorem _root_.GlobalTheory.T.submodulePatchAtPrime_isLattice_locP : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E A → Submodule.IsFullLattice E B → Submodule.IsLattice E (patchAt P A B) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro E _ _ _ n P A B hA hB
  first
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA hB
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA.toIsLattice hB.toIsLattice
