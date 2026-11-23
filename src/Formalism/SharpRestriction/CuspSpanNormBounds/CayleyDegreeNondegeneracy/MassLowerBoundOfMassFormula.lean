module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeIsIntegralOfUnimodular
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
