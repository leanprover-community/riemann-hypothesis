module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_packingSet_measure_ge_covolume : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  first | exact @GlobalTheory.packing_set_covolume_le | exact GlobalTheory.packing_set_covolume_le | (intros; apply GlobalTheory.packing_set_covolume_le <;> assumption)
