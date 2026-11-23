module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
