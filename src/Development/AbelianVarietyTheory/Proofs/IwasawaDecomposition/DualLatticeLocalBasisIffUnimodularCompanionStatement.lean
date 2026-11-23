module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeLocalBasisIffUnimodularCompanion
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  first | exact @GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | exact GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | (intros; apply GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N <;> assumption)
