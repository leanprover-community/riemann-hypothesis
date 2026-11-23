module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullback
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  first | exact @GlobalTheory.MumFam.FactorAdj.exists_pull | exact GlobalTheory.MumFam.FactorAdj.exists_pull | (intros; apply GlobalTheory.MumFam.FactorAdj.exists_pull <;> assumption)
