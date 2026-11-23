module

public import GroundTheory.LocalFields.LocalArtinMap
public import GroundTheory.ProfiniteCohomology.CyclicCupGaloisDefs
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolDefs
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField

section Sep

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def brauerInvZOfIsSepClosure : cohomology (galUnitsZ K Ω) 2 →+ QZ :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ K Ω

theorem brauerInvZOfIsSepClosure_bijective : Function.Bijective (brauerInvZOfIsSepClosure K Ω) :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ_bijective K Ω

variable {K Ω}

theorem brauerInvZOfIsSepClosure_galCupClass (χ : Additive Gal(Ω/K) →ₜ+ QZ) (a : Kˣ) (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (localArtinMap K Ω a ⟨y, hy⟩ : Ω)) :
    brauerInvZOfIsSepClosure K Ω (galCupClass K Ω χ a) = χ (Additive.ofMul g) :=
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  brauerInvZ_galCupClass χ a g hg

end Sep

end GroundTheory.ProfCoh
