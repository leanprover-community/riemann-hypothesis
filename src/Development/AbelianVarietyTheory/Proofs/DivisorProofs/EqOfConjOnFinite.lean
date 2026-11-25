module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

end GlobalTheory.ConjCharUnique
