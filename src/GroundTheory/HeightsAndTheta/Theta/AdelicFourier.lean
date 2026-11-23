module

public import Mathlib.NumberTheory.NumberField.AdeleRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Measure Matrix Module TensorProduct
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical nonZeroDivisors

noncomputable section

set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]


variable (K X) in
abbrev AdelicPoints : Type _ := 𝔸[K] ⊗[K] X

instance : TopologicalSpace (AdelicPoints K X) := moduleTopology 𝔸[K] (AdelicPoints K X)

instance : IsModuleTopology 𝔸[K] (AdelicPoints K X) := ⟨rfl⟩

instance : IsTopologicalAddGroup (AdelicPoints K X) := IsModuleTopology.topologicalAddGroup 𝔸[K] _

instance : MeasurableSpace (AdelicPoints K X) := borel _

instance : BorelSpace (AdelicPoints K X) := ⟨rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]



variable (B : LinearMap.BilinForm K X)




end

end GroundTheory.Heights₂.Theta
