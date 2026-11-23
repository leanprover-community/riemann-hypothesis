module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntCAtState
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd :
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
      GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt →
      GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform →
      GlobalTheory.HeckeSupSt.HeckeReadTie →
      StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
        _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
        ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
          (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)),
          LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' →
          HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
          IntC (SOf x) (SbD (Dof x)) θ hL' :=
  _root_.GlobalTheory.HeightCounting.RatSide.intC_of_lvlPsi_stabC_heckeRd
end
