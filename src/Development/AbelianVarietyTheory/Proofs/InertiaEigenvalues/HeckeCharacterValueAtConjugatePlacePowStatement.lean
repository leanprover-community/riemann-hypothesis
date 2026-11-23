module

public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePow
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  first | exact @GlobalTheory.ConjLocVal.value_at_conj_place | exact GlobalTheory.ConjLocVal.value_at_conj_place | (intros; apply GlobalTheory.ConjLocVal.value_at_conj_place <;> assumption)
