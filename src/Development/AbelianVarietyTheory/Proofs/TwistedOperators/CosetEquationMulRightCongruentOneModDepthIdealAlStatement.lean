module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAl
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.coset_equation_mul_right_congruent_one_mod_depthIdeal_alt : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  first | exact @GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | exact GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal | (intros; apply GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal <;> assumption)
