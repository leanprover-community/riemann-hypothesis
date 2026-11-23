module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_fixed (B : Base) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, B'.toPre = B.toPre ∧ B'.KsC = B.KsC ∧ ∀ z ∈ S, z ∈ B'.fixedCoefficientFieldInComplex := by
  obtain ⟨B', h, h'⟩ := BaseEnl.exists_enl B S hS
  refine ⟨{ B' with LL0 := ⊤, coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm, Ks_le := le_top,
                    rootOfUnity_eightQ_mem_coeffGaloisSubfield := B'.rootOfUnity_eightQ_mem_coeffGaloisSubfield.imp fun _ hz => ⟨trivial, hz.2⟩ }, h.1, h.KsC_eq, fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := h' z hz
  exact ⟨x, trivial, hx⟩

end GlobalTheory.Mem.Top.Inh

end
