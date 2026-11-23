module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain
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

theorem _root_.GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  first | exact @GlobalTheory.ExchLatPf.exchLat | exact GlobalTheory.ExchLatPf.exchLat | (intros; apply GlobalTheory.ExchLatPf.exchLat <;> assumption)
