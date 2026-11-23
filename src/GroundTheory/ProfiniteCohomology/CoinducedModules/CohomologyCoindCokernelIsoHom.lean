module

public import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
public import GroundTheory.ProfiniteCohomology.CoinducedModules
public import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

instance isDiscreteRep_coindShortComplex_X₁ : IsDiscreteRep (coindShortComplex A).X₁ :=
  (inferInstance : IsDiscreteRep A)

instance isDiscreteRep_coindShortComplex_X₂ : IsDiscreteRep (coindShortComplex A).X₂ :=
  (inferInstance : IsDiscreteRep (discreteCoind k G A))

instance isDiscreteRep_coindShortComplex_X₃ : IsDiscreteRep (coindShortComplex A).X₃ :=
  (inferInstance : IsDiscreteRep (coindCokernel A))

noncomputable def coindδ (n : ℕ) : cohomology (coindCokernel A) n ⟶ cohomology A (n + 1) :=
  δ (coindShortComplex_shortExact A) n (n + 1) rfl

instance epi_coindδ (n : ℕ) : Epi (coindδ A n) :=
  (cohomology_exact₁ (coindShortComplex_shortExact A) n (n + 1) rfl).epi_f
    ((isZero_cohomology_discreteCoind (k := k) (G := G) (X := A) n).eq_of_tgt _ _)

instance mono_coindδ_succ (n : ℕ) : Mono (coindδ A (n + 1)) :=
  (cohomology_exact₃ (coindShortComplex_shortExact A) (n + 1) (n + 2) rfl).mono_g
    ((isZero_cohomology_discreteCoind (k := k) (G := G) (X := A) n).eq_of_src _ _)

instance isIso_coindδ_succ (n : ℕ) : IsIso (coindδ A (n + 1)) :=
  isIso_of_mono_of_epi _

noncomputable def cohomologyCoindCokernelIso (n : ℕ) :
    cohomology (coindCokernel A) (n + 1) ≅ cohomology A (n + 2) :=
  asIso (coindδ A (n + 1))

end GroundTheory.ProfCoh
