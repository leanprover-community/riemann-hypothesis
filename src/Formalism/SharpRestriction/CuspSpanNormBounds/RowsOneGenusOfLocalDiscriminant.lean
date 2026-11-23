module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
public import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfCyclic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

private theorem rows_span_eq_top_of_unimodular (S : Formalism.BasicNotions.HSpace E) {Λ : Submodule (𝓞 E) S.V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    Submodule.span E (Λ : Set S.V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU S.herm hL


theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨{ toIsLattice := hM, span_eq_top := rows_span_eq_top_of_unimodular S hM.fg huM }, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

section Rows

open Formalism.BasicNotions Formalism.MainNotions.BridgeLemma₂

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
